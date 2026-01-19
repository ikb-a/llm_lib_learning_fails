"""
Plot individual soft use lemma & task survival functions for the original
LEGO-Prover logs.

NOTE: Run data_analysis/plot_lemma_survival.py and data_analysis/plot_tasks_vs_threshold.py 
      to read the recorded similarity data and generate the lemma and task survival 
      plots in the paper.
"""

import re
import os
import json
from data_analysis.utils import extract_lemmas
from tqdm import tqdm
from collections import defaultdict
import numpy as np
import copy


#from data_analysis.calc_common_ancestors_reuse import load_afp_lemmas

AFP_REGEX = re.compile(
    r"(?:lemma|theorem)\s+[^:]+?\s*:(?:[\s\S](?!lemma|theorem))+?qed"
)


# Proofs where extraction of body fails because the LLM
# directly used sledgehammer to solve the proof (i.e., there
# is no proof body)
DIRECT = r"""```isabelle
theory mathd_numbertheory_239
imports Complex_Main 
begin

(* no helper function required in this theorem *)

(* formal statement copy from the input *)
theorem mathd_numbertheory_239 :
  "(\<Sum> k \<in>{1..<13}. k) mod 4 = (2::nat)"
  sledgehammer

end
```"""

DIRECT2 = r"""```isabelle
theory mathd_numbertheory_185
  imports Complex_Main
begin

(* no helper function required in this theorem *)

(* formal statement copy from the input *)
theorem mathd_numbertheory_185:
  fixes n ::nat
  assumes "n mod 5 = 3" 
  shows "(2 * n) mod 5 = 1"
  sledgehammer

end
```"""

DIRECT3 = r"""```isabelle
theory mathd_numbertheory_81
  imports Complex_Main 
begin

(* formal statement copy from the input *)
theorem mathd_numbertheory_81:
  "71 mod 3 = (2::nat)"
  sledgehammer

end
```"""

DIRECT4 = r"""```isabelle
theory mathd_numbertheory_200
imports Complex_Main 
begin

(* no helper function required in this theorem *)

(* formal statement copy from the input *)
theorem mathd_numbertheory_200:
  "139 mod 11 = (7::nat)"
  sledgehammer

end
```"""

DIRECT5 = r"""```isabelle
theory mathd_numbertheory_961
  imports Complex_Main 
begin

(* no helper function required in this theorem *)

(* formal statement copy from the input *)
theorem mathd_numbertheory_961:
  "2003 mod 11 = (1::nat)"
  sledgehammer

end
```"""

DIRECT6 = r"""```isabelle
theory mathd_algebra_304
imports Complex_Main
begin

(* formal statement copy from the input *)
theorem mathd_algebra_304:
  "91^2 = (8281::nat)"
  sledgehammer

end
```"""

DIRECT7 = r"""```isabelle
theory mathd_algebra_176
imports Complex_Main
begin

(* formal statement copy from the input *)
theorem mathd_algebra_176:
  fixes x ::real
  shows "(x + 1)^2 * x = x^3 + 2 * x^2 + x"
  sledgehammer

end
```"""

DIRECT8=r"""```isabelle
theory mathd_numbertheory_169
imports Complex_Main
begin

(* formal statement copy from the input *)
theorem mathd_numbertheory_169:
  "gcd (fact 20) 200000 = (40000::nat)"
  sledgehammer

end
```"""

DIRECT9 = r"""```isabelle
theory mathd_numbertheory_252
imports Complex_Main
begin

(* formal statement copy from the input *)
theorem mathd_numbertheory_252:
  "(fact 7) mod 23 = (3::nat)"
  sledgehammer

end
```"""

ALL_DIRECT = [DIRECT, DIRECT2, DIRECT3, DIRECT4, DIRECT5, DIRECT6, DIRECT7, DIRECT8, DIRECT9]



from Levenshtein import distance as lev_distance
import random

random.seed(42)

COMMENT_REGEX = re.compile(r"\(\*[\s\S]*?\*\)")


def similarity(lemma, solution):
    """Modified, normalized, edit distance from lemma to solution

    Remove ISAR comments from solution.
    Convert both into white space separated tokens.

    Compute Levenshtein distance with free insertion (note: token level, not character level).
    Normalize to a value between 0 and 1 by dividing by the length of the input lemma.

    Subtract from 1 and return

    0 means total replacement of all characters.
    1 means exact match

    >>> similarity('hi there', 'and then they said hi and there just like that')
    1.0
    >>> similarity('hi there', 'and then just like that')
    0.0
    """
    solution = re.sub(COMMENT_REGEX, "", solution)  # Remove ISAR comments
    solution_tok = solution.split()
    lemma_tok = lemma.split()

    final_sim = 1 - lev_distance(lemma_tok, solution_tok, weights=(0, 1, 1)) / len(
        lemma_tok
    )  # Free insertion
    return final_sim


def _update_reuse(
    theshold_filtered_children,
    answers,
    threshold,
    reused_lemmas_count,
    tasks_with_reuse,
):
    for lemma in theshold_filtered_children:
        if (
            len(theshold_filtered_children[lemma]) < 2
        ):  # Already know there is no reuse; skip
            continue

        # Only keep tasks where solution has at least the similarity required
        theshold_filtered_children[lemma] = set(
            task
            for task in theshold_filtered_children[lemma]
            if similarity(lemma, answers[task]) >= threshold
        )

        # If more than 2 tasks are left (i.e., reuse), then add this to our count
        if len(theshold_filtered_children) >= 2:
            reused_lemmas_count[-1] += 1
            tasks_with_reuse |= theshold_filtered_children[lemma]




def _update_use(
    theshold_filtered_children,
    answers,
    threshold,
    used_lemmas_count,
    tasks_with_use,
):
    for lemma in tqdm(theshold_filtered_children):
        if len(theshold_filtered_children[lemma]) < 1:  # Not used in anything, skip
            continue

        # Only keep tasks where solution has at least the similarity required
        theshold_filtered_children[lemma] = set(
            task
            for task in theshold_filtered_children[lemma]
            if similarity(lemma, answers[task]) >= threshold
        )

        # If any tasks left, add this to our count
        if len(theshold_filtered_children) >= 1:
            used_lemmas_count[-1] += 1
            tasks_with_use |= theshold_filtered_children[lemma]


def process_run(datapath, run_idx):

    print("=" * 100)
    print(datapath)

    # Load data
    with open(datapath, 'r') as infile:
        successes = json.load(infile)

    print(f"{len(successes)} Solved problems")

    # Create dictionary to solutions
    answers = {}
    children = defaultdict(
        lambda: set()
    )  # Map lemmas to a set of its children solved tasks
    for succ in successes:
        assert succ["success"]

        if  succ["prover_conversation"]["ai"] in ALL_DIRECT:
            print("SKIP")
            continue

        answers[succ["task"]] = re.sub(COMMENT_REGEX, "", succ["prover_conversation"]["ai"])

        # For each solved problem, find its child lemmas
        # & count the occurences of each child lemma
        # print('find parents', flush=True)
        lemmas = extract_lemmas(succ)
        for lemma in lemmas:
            children[lemma].add(succ["task"])
    

    # Plot instances of reuse as a function of similarity threshold
    used_lemmas_count = []  # Number of lemmas reused in at least 2 tasks
    task_with_use_count = (
        []
    )  # Number of tasks with a lemma of similarity at least THRES that in turn has sim of at lesat THRES with another 
    
    reused_lemmas_count = []
    task_with_reuse_count = []

    thresholds = [0.05 * x for x in range(21)]

    
    # Initial threshold is similarity 0, therefore any task where
    # the lemma showed up in the prompt is OK
    use_theshold_filtered_children = copy.deepcopy(children)
    reuse_theshold_filtered_children = copy.deepcopy(children)

    for threshold in thresholds:
        used_lemmas_count.append(0)

        tasks_with_use = set()
        _update_use(
            use_theshold_filtered_children,
            answers,
            threshold,
            used_lemmas_count,
            tasks_with_use,
        )
        task_with_use_count.append(len(tasks_with_use))

        # REUSE
        reused_lemmas_count.append(0)
        tasks_with_reuse = set()
        _update_reuse(
            reuse_theshold_filtered_children,
            answers,
            threshold,
            reused_lemmas_count,
            tasks_with_reuse,
        )
        task_with_reuse_count.append(len(tasks_with_reuse))

    assert len(used_lemmas_count) == len(thresholds)

    return (
        -1,
        -1,
        thresholds,
        used_lemmas_count,
        task_with_use_count,
        len(successes),
        reused_lemmas_count,
        task_with_reuse_count
    )


def flatten(input_list):
    res = []
    for l in input_list:
        res += l
    return np.array(res)


def main(data_paths, output_path):
    amort_path = output_path

    thresholds = None
    used_lemmas_count = []
    task_with_use_count = []
    num_successes = []

    amortized_data = {}

    i = 0 
    datapath = data_paths
    (
        _,
        _,
        zthesholds,
        zused_lemmas_count,
        ztask_with_use,
        znum_success,
        zreused_lemmas_count,
        ztask_with_reuse_count
    ) = process_run(datapath, i + 1)

    if thresholds is None:
        thresholds = zthesholds
    else:
        assert thresholds == zthesholds
    num_successes.append(znum_success)

    used_lemmas_count.append(zused_lemmas_count)
    task_with_use_count.append(ztask_with_use)


    amortized_data["thresholds"] = thresholds
    amortized_data["used_lemmas_count"] = used_lemmas_count
    amortized_data["task_with_use_count"] = task_with_use_count
    amortized_data["num_successes"] = num_successes
    amortized_data["reused_lemmas_count"] = zreused_lemmas_count
    amortized_data["task_with_reuse_count"] = ztask_with_reuse_count

    with open(amort_path, "w") as outfile:
        json.dump(amortized_data, outfile, indent=2, sort_keys=True)
    

if __name__ == "__main__":
    import doctest
    from pathlib import Path

    SPLITS = ['gpt_informal_test.json', 'gpt_informal_valid.json', 'human_informal_test.json', 'human_informal_valid.json']
    ROOT = Path('data_analysis/ori_lp_reuse_analysis/lego_result/')

    for input_path, output_path in [(ROOT/split, ROOT/f'soft_sim_{split}') for split in SPLITS]:
        main(
            data_paths=input_path,
            output_path=output_path,
        )
