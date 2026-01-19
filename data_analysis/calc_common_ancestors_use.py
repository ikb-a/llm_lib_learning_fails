"""
Plot individual soft use lemma & task survival functions.

NOTE: Run data_analysis/plot_lemma_survival.py and data_analysis/plot_tasks_vs_threshold.py 
      to read the recorded similarity data and generate the lemma and task survival 
      plots in the paper.
"""

import re
import os
import json
from utils import extract_lemmas2 as extract_lemmas
from direct_reuse_analysis import print_frequency
from tqdm import tqdm
from collections import defaultdict
import matplotlib.pyplot as plt
import numpy as np
import copy
from plot_utils import load_formalizer_free_lemmas

#from data_analysis.calc_common_ancestors_reuse import load_afp_lemmas

AFP_REGEX = re.compile(
    r"(?:lemma|theorem)\s+[^:]+?\s*:(?:[\s\S](?!lemma|theorem))+?qed"
)


def load_afp_lemmas(root_directory) -> set:
    afp_lemmas = set()
    for root, _, files in tqdm(os.walk(root_directory)):
        for filename in files:
            if not filename.endswith(".thy"):
                continue
        
            with open(os.path.join(root, filename), "r") as infile:
                data = infile.read()
            # Remove comments
            data = re.sub(COMMENT_REGEX, "", data)
            # Remove redundant newlines
            data = "\n".join(data.split("\n"))
            afp_lemmas.update(re.findall(AFP_REGEX, data))

    print(f"Loaded {len(afp_lemmas)} AFP lemmas")
    return afp_lemmas

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


def load_successes(results_path):
    """
    Iterate through LEGO-Prover json logs folder and load all
    succesful attempts.
    """
    # ======================================================
    # Loading data.
    # Iterate through dir, check which suceeded, store filtered json dicts in a list.
    lego_results = []

    for attempt in tqdm(os.listdir(results_path), disable=True):
        if not attempt.endswith(".json"):
            continue

        with open(os.path.join(results_path, attempt), "r") as infile:
            attempt_data = json.load(infile)

        if not attempt_data["success"]:
            continue
        lego_results.append(attempt_data)

    return lego_results


def find_parents(lego_results) -> tuple[dict[str, set], dict[str, set]]:
    """
    Find lemmas directly retrieved and used in generating solution.
    """
    parents = {}  # Map solved task to a set of its parents
    children = defaultdict(
        lambda: set()
    )  # Map lemmas to a set of its children solved tasks

    for succesful_run in lego_results:
        assert succesful_run["success"]
        task = succesful_run["task"]
        lemmas = set(extract_lemmas(succesful_run))
        parents[task] = lemmas

        for lemma in lemmas:
            children[lemma].add(task)

    return children, parents


def _update(
    theshold_filtered_children,
    answers,
    threshold,
    reused_lemmas_count,
    tasks_with_reuse,
):
    for lemma in theshold_filtered_children:
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
            reused_lemmas_count[-1] += 1
            tasks_with_reuse |= theshold_filtered_children[lemma]


def process_run(datapath, run_idx, output_path, unrelated_lemmas):
    os.makedirs(output_path, exist_ok=True)

    print("=" * 100)
    print(datapath)
    assert f"run{run_idx}" in str(datapath) or f"_{run_idx}/" in str(datapath) or f"_idx{run_idx - 1}" in str(datapath)

    # Load data
    successes = load_successes(datapath)

    print(f"{len(successes)} Solved problems")

    # Create dictionary to solutions
    answers = {}
    for succ in successes:
        assert succ["success"]
        answers[succ["task"]] = re.sub(COMMENT_REGEX, "", succ["conversations"][0][-1])

    # For each solved problem, find its child lemmas
    # & count the occurences of each child lemma
    # print('find parents', flush=True)
    children, parents = find_parents(successes)

    # Report distribution
    print(
        f"{sum(1 if len(children[x])==1 else 0 for x in children)/len(children)} of retrieved lemmas not reused"
    )
    print(
        "Frequency distribution: Number of tasks that use a given retrieved lemma",
        flush=True,
    )
    print_frequency(children)

    # Get non-retrieved similarity
    clean_lemmas = load_formalizer_free_lemmas(datapath, silent=True)
    non_retrieved_sim = []
    for task in parents:
        lemmas = parents[task]
        remaining = clean_lemmas - lemmas
        for lemma in remaining:
            non_retrieved_sim.append(similarity(lemma, answers[task]))

    # Plot instances of reuse as a function of similarity threshold
    reused_lemmas_count = []  # Number of lemmas reused in at least 2 tasks
    task_with_reuse_count = (
        []
    )  # Number of tasks with a lemma of similarity at least THRES that in turn has sim of at lesat THRES with another task
    thresholds = [0.05 * x for x in range(21)]

    non_retr_count = []  # Number of non-retrieved lemmas surviving
    non_retr = clean_lemmas - set(children.keys())
    non_retr_threshold_filtered = {
        lemma: set(task for task in parents) for lemma in non_retr
    }  # Initially all non-retr suff similar to all tasks

    unrelated_count = []
    unrelated_threshold_filtered = {
        lemma: set(task for task in parents) for lemma in unrelated_lemmas
    }

    # Initial threshold is similarity 0, therefore any task where
    # the lemma showed up in the prompt is OK
    theshold_filtered_children = copy.deepcopy(children)

    for threshold in thresholds:
        reused_lemmas_count.append(0)
        non_retr_count.append(0)
        unrelated_count.append(0)

        tasks_with_reuse = set()
        _update(
            theshold_filtered_children,
            answers,
            threshold,
            reused_lemmas_count,
            tasks_with_reuse,
        )
        _update(non_retr_threshold_filtered, answers, threshold, non_retr_count, set())
        _update(
            unrelated_threshold_filtered, answers, threshold, unrelated_count, set()
        )

        task_with_reuse_count.append(len(tasks_with_reuse))

    assert len(reused_lemmas_count) == len(thresholds)
    print(unrelated_count)

    plt.plot(thresholds, reused_lemmas_count)
    plt.xlabel("Similarity Threshold")
    plt.ylabel("% of Non-Retrieved Lemmas Meeting Similarity Threshold in 1 Solution")
    ax = plt.gca()
    ax.axvline(np.average(non_retrieved_sim), color="red", linestyle="--")  # type: ignore
    ax2 = ax.twinx()
    ax2.plot(
        thresholds, np.array(non_retr_count) / non_retr_count[0] * 100, color="red"
    )
    ax2.plot(
        thresholds, np.array(unrelated_count) / unrelated_count[0] * 100, color="orange"
    )
    _, name = os.path.split(output_path)
    plt.title(name)
    plt.savefig(
        os.path.join(output_path, f"ONE_TASK_lemma_count_sim_thres_{run_idx}.png")
    )
    plt.close()

    plt.plot(thresholds, np.array(task_with_reuse_count) / len(successes) * 100)
    plt.xlabel("Similarity Threshold")
    plt.ylabel("Percentage of Solved Tasks using lemma")

    _, name = os.path.split(output_path)
    plt.title(name)
    plt.savefig(
        os.path.join(output_path, f"ONE_TASK_task_count_sim_thres_{run_idx}.png")
    )
    plt.close()

    return (
        -1,
        -1,
        non_retrieved_sim,
        thresholds,
        reused_lemmas_count,
        task_with_reuse_count,
        len(successes),
        non_retr_count,
        unrelated_count,
    )


def flatten(input_list):
    res = []
    for l in input_list:
        res += l
    return np.array(res)


def main(data_paths, output_path, unrelated_lemmas, amortized_data_name: str):
    amort_path = os.path.join(output_path, amortized_data_name + ".json")
    if os.path.exists(amort_path):
        with open(amort_path, "r") as infile:
            amortized_data = json.load(infile)
    else:
        amortized_data = {}

    if len(amortized_data) == 0:
        non_retrieved_sim = []
        thresholds = None
        reused_lemmas_count = []
        task_with_reuse_count = []
        num_successes = []
        non_retr_count = []
        unrelated_count = []

        for i, datapath in enumerate(data_paths):
            (
                _,
                _,
                znon_retrieved_sim,
                zthesholds,
                zreused_lemmas_count,
                ztask_with_reuse,
                znum_success,
                znon_retr_count,
                zunrel_count,
            ) = process_run(datapath, i + 1, output_path, unrelated_lemmas)

            if thresholds is None:
                thresholds = zthesholds
            else:
                assert thresholds == zthesholds
            num_successes.append(znum_success)

            non_retrieved_sim.append(znon_retrieved_sim)
            reused_lemmas_count.append(zreused_lemmas_count)
            task_with_reuse_count.append(ztask_with_reuse)
            non_retr_count.append(znon_retr_count)
            unrelated_count.append(zunrel_count)

        amortized_data["non_retrieved_sim"] = non_retrieved_sim
        amortized_data["thresholds"] = thresholds
        amortized_data["reused_lemmas_count"] = reused_lemmas_count
        amortized_data["task_with_reuse_count"] = task_with_reuse_count
        amortized_data["num_successes"] = num_successes
        amortized_data["non_retr_count"] = non_retr_count
        amortized_data["unrelated_count"] = unrelated_count

    if not os.path.exists(amort_path):
        with open(amort_path, "w") as outfile:
            json.dump(amortized_data, outfile, indent=2, sort_keys=True)

    non_retrieved_sim = amortized_data["non_retrieved_sim"]
    thresholds = amortized_data["thresholds"]
    reused_lemmas_count = amortized_data["reused_lemmas_count"]
    task_with_reuse_count = amortized_data["task_with_reuse_count"]
    num_successes = amortized_data["num_successes"]
    non_retr_count = amortized_data["non_retr_count"]
    unrelated_count = amortized_data["unrelated_count"]

    # Flatten to single array
    non_retrieved_sim = flatten(non_retrieved_sim)
    # Flatten & plot
    reused_lemmas_count = np.array(reused_lemmas_count).sum(axis=0).flatten()
    non_retr_count = np.array(non_retr_count).sum(axis=0).flatten()
    unrelated_count = np.array(unrelated_count).sum(axis=0).flatten()

    plt.plot(thresholds, reused_lemmas_count)
    plt.xlabel("Similarity Threshold")
    plt.ylabel("Retrieved Lemmas reused in 2 tasks")
    ax = plt.gca()
    ax.axvline(np.average(non_retrieved_sim), color="red", linestyle="--")

    ax2 = ax.twinx()
    ax2.plot(
        thresholds, np.array(non_retr_count) / non_retr_count[0] * 100, color="red"
    )
    ax2.plot(
        thresholds, np.array(unrelated_count) / unrelated_count[0] * 100, color="orange"
    )
    ax2.set_ylabel(
        "% of Non-Retrieved Lemmas Meeting Similarity Threshold in 1 Solutions"
    )

    _, name = os.path.split(output_path)
    plt.title(name)
    plt.savefig(
        os.path.join(output_path, f"ONE_TASK_lemma_count_sim_thres_aggregate.png")
    )
    plt.close()

    task_with_reuse_count = np.array(task_with_reuse_count).sum(axis=0).flatten()
    num_successes = sum(num_successes)
    plt.plot(thresholds, np.array(task_with_reuse_count) / num_successes * 100)
    plt.xlabel("Similarity Threshold")
    plt.ylabel("Percentage of Solved Tasks using a reused lemma")
    ax = plt.gca()
    ax.axvline(np.average(non_retrieved_sim), color="red", linestyle="--")

    _, name = os.path.split(output_path)
    plt.title(name)
    plt.savefig(
        os.path.join(output_path, f"ONE_TASK_task_count_sim_thres_aggregate.png")
    )
    plt.close()


if __name__ == "__main__":
    import doctest

    doctest.testmod()

    afp_lemmas = load_afp_lemmas("AFP/afp-2019-08-19/thys/")

    amortized_data = "afp"

    for input_path, output_path, unrelated in [
        # o3-mini, experiment 4
        (
            [
                f"ablation_experiment_results/22_exp4_test_split_o3mini/run{i}/checkpoints/22_exp4_test_split_o3mini_{i}/json_logs/"
                for i in range(1, 4)
            ],
            "data_analysis/calc_common_ancestors_ONE_TASK/exp4_o3mini",
            afp_lemmas,
        ),
        # 4o, experiment 5
        (
            [
                f"ablation_experiment_results/21_exp5_test_split_4o_prompt2/checkpoints/21_exp5_test_split_4o_prompt2_{i}/json_logs/"
                for i in range(1, 4)
            ],
            "data_analysis/calc_common_ancestors_ONE_TASK/exp5_4o",
            afp_lemmas,
        ),
        # Exp 1, 4o-mini
        (
            [
                f"ablation_experiment_results/20_exp1_test/run{i}/checkpoints/20_exp1_test_{i}/json_logs/"
                for i in range(1, 4)
            ],
            "data_analysis/calc_common_ancestors_ONE_TASK/exp1_4omini",
            afp_lemmas,
        ),
        # Llama 3.1, 10%
        (
            [
                f"ablation_experiment_results_arr_sept/10_perc_test/lp/re1_exp4_Meta-Llama-3.1-8B-Instruct_idx{i-1}/json_logs/"
                for i in range(1, 4)
            ],
            "data_analysis/calc_common_ancestors_ONE_TASK/llama3.1_10perc",
            afp_lemmas,
        ),
        #Qwen3 10%
        (
            [
                f"ablation_experiment_results_arr_sept/10_perc_test/lp_qwen/re1_exp4_qwen3_14B_Qwen3-14B_idx{i-1}/json_logs/"
                for i in range(1, 4)
            ],
            "data_analysis/calc_common_ancestors_ONE_TASK/10perc_qwen3",
            afp_lemmas,
        ),
        # Llama 3.1, 100%
        (
            [
                f"ablation_experiment_results_arr_sept/full_test/lp/full_re1_exp4_Meta-Llama-3.1-8B-Instruct_idx{i-1}/json_logs/"
                for i in range(1, 4)
            ],
            "data_analysis/calc_common_ancestors_ONE_TASK/100perc_llama3.1",
            afp_lemmas,
        ),

    ]:
        main(
            data_paths=input_path,
            output_path=output_path,
            unrelated_lemmas=unrelated,
            amortized_data_name=amortized_data,
        )
