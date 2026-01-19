"""
Search for direct use (either verbatim or name reuse) in the 
output of LEGO-Prover.

The raw data is available for download at https://archive.org/details/readme_20260118
"""

import json
from collections import defaultdict, Counter
import os
from utils import extract_lemmas2 as extract_lemmas
from utils import extract_lemma_names, fmt_proof
from tqdm import tqdm
from typing import Any


def print_frequency(dict: dict[Any, list]) -> None:
    """
    For a dictionary mapping values to lists, print a summary
    of the distribution of list lengths.
    """
    print(json.dumps(Counter(len(x) for x in dict.values()), sort_keys=True, indent=2))


def print_frequency_avg(dict: dict[Any, list], total: int) -> None:
    """
    For a dictionary mapping values to lists, print a summary
    of the distribution of list lengths -- normalize lengths by total.
    """
    freq = Counter(len(x) for x in dict.values())
    keys = sorted(list(freq.keys()))
    print("{")
    for key in keys:
        print(f"\t{key}: {freq[key]}/{total} = {freq[key]/total * 100:.2f}%")
    print("}")


def summarize_top_n_by_freq(
    save_loc: str,
    filename_prefix: str,
    lego_results: dict,
    lemma_to_task: dict[str, list],
    k: int,
    description: str,
) -> None:
    """
    Print a detailed report about the lemmas appearing in the most solutions.

    save_loc: where to save the report
    filename_prefix: prefix for the report's filename
    lego_results: the full LEGO-Prover log file
    lemma_to_task: dictionary from lemmas to a list of tasks they appear in
    k: the number of lemmas to produce a detailed report for
    description: a description of how `lemma_to_task` was created.
    """
    os.makedirs(save_loc, exist_ok=True)

    lemmas = list(lemma_to_task.keys())
    # Tie break by the string
    lemmas.sort(key=lambda x: (len(lemma_to_task[x]), x), reverse=True)

    lemmas = lemmas[:k]

    for lemma in lemmas:
        lemma_names = extract_lemma_names(lemma)

        if len(lemma_names) == 0:
            print(lemma)
            exit(-1)

        with open(
            os.path.join(
                save_loc,
                f"{len(lemma_to_task[lemma])}_{filename_prefix}{lemma_names[0]}.md",
            ),
            "w",
        ) as outfile:
            print(f"# {', '.join(lemma_names)}\n", file=outfile)
            print(description, file=outfile)
            print("", file=outfile)
            print(f"Frequency: {len(lemma_to_task[lemma])}", file=outfile)
            print("", file=outfile)
            print(f"Lemma:\n```isabelle\n{lemma}\n```", file=outfile)

            for i, task in enumerate(lemma_to_task[lemma]):
                print(
                    f"\n\n## Usage {i+1} of {len(lemma_to_task[lemma])}:", file=outfile
                )
                print("### Problem:", file=outfile)
                print(f"Task name: `{os.path.split(task)[1]}`\n", file=outfile)
                task_details = [x for x in lego_results if x["task"] == task]
                assert len(task_details) == 1, task_details
                task_details = task_details[0]
                print(f"{task_details['context']['informal_statement']}", file=outfile)
                print("### Informal Proof:", file=outfile)
                print(f"{task_details['context']['informal_proof']}", file=outfile)

                print("### Solution:", file=outfile)
                print(
                    f"```isabelle\n{task_details['context']['formal_statement']}\n```",
                    file=outfile,
                )
                print("AI Generated completion (lemma lines higlighted):", file=outfile)
                print(
                    f"{fmt_proof(task_details['conversations'][0][-1] , lemma_names=lemma_names)}",  # ["prover_conversation"]["ai"]
                    file=outfile,
                )


def main(results_path: str, results_name: str):
    total_questions = 0
    # ======================================================
    # Loading data.
    # Iterate through dir, check which suceeded, store filtered json dicts in a list.
    lego_results = []

    for attempt in tqdm(os.listdir(results_path), disable=True):
        if not attempt.endswith(".json"):
            continue
        total_questions += 1
        with open(os.path.join(results_path, attempt), "r") as infile:
            attempt_data = json.load(infile)

        if not attempt_data["success"]:
            continue
        lego_results.append(attempt_data)

    print("===============================")
    print(results_name)

    used_in_prompt = defaultdict(lambda: list())
    used_in_solution = defaultdict(lambda: list())
    name_used_in_solution = defaultdict(lambda: list())
    sub_lemmas = {}

    tasks_using_lemma_verbatim = set()
    tasks_using_lemma_name = set()

    for succesful_run in lego_results:
        assert succesful_run["success"]
        task = succesful_run["task"]
        lemmas = extract_lemmas(succesful_run)

        for lemma in lemmas:
            used_in_prompt[lemma].append(task)
            if (
                lemma in succesful_run["conversations"][0][-1]
            ):  # ["prover_conversation"]["ai"]:
                used_in_solution[lemma].append(task)
                tasks_using_lemma_verbatim.add(task)

            if any(
                name
                in succesful_run["conversations"][0][
                    -1
                ]  # ["prover_conversation"]["ai"]
                for name in extract_lemma_names(lemma)
            ):
                name_used_in_solution[lemma].append(task)
                tasks_using_lemma_name.add(task)

            sub_lemmas[lemma] = extract_lemma_names(lemma)

    print(f"Succesful Prover Attempts: {len(lego_results)}/{total_questions}")
    print(
        f"Questions using a lemma verbatim: {len(tasks_using_lemma_verbatim)}/{len(lego_results)} = {len(tasks_using_lemma_verbatim)/len(lego_results)*100:.2f}%"
    )
    print(
        f"Questions using a lemma name: {len(tasks_using_lemma_name)}/{len(lego_results)} = {len(tasks_using_lemma_name)/len(lego_results) * 100:.2f}%"
    )

    print()
    print(f"Total number lemmas used in at least one prompt: {len(used_in_prompt)}")
    print(
        f"Total number of lemmas appearing verbatim in LLM output: {len(used_in_solution)}"
    )

    print(
        "\nNumber of Lemmas (i.e., skill in prompt) containing $N$ `theorem` or `lemma` statements:"
    )
    print_frequency_avg(sub_lemmas, len(used_in_prompt))

    print(
        "\nNumber of Lemmas used in $N$ tasks (specifically, contained in the task's final prompts to the solver)"
    )
    print_frequency_avg(used_in_prompt, len(used_in_prompt))

    print(
        "\nNumber of Lemma reproduced exactly in $N$ LLM outputs (i.e., $N$ is the number of tasks whose solutions used the Lemma verbatim):"
    )
    print_frequency_avg(used_in_solution, len(used_in_prompt))

    print(
        "\nNumber of Lemmas whose *name* appears in $N$ LLM outputs (i.e., $N$ is the number of tasks whose solutions contained the *name* of the Lemma):"
    )
    print_frequency_avg(name_used_in_solution, len(used_in_prompt))

    summarize_top_n_by_freq(
        save_loc=f"data_analysis/direct_reuse/{results_name}/exact_match",
        filename_prefix="exact_",
        lego_results=lego_results,
        lemma_to_task=used_in_solution,
        k=5,
        description="Tasks where a provided skill is reproduced verbatim",
    )

    summarize_top_n_by_freq(
        save_loc=f"data_analysis/direct_reuse/{results_name}/name_match",
        filename_prefix="name_",
        lego_results=lego_results,
        lemma_to_task=name_used_in_solution,
        k=5,
        description="Tasks where a provided skill's *name* is reproduced verbatim",
    )


if __name__ == "__main__":
    for input_path, name in (
        # [
        #     (
        #         f"ablation_experiment_results_arr_sept/10_perc_test/lp/re1_exp4_Meta-Llama-3.1-8B-Instruct_idx{i-1}/json_logs/",
        #         f"llama3.1_10perc_run{i}",
        #     )
        #     for i in range(1, 4)
        # ]
                [
            (
                f"ablation_experiment_results/21_exp5_test_split_4o_prompt2/checkpoints/21_exp5_test_split_4o_prompt2_{i}/json_logs/",
                f"exp5_4o_run{i}",
            )
            for i in range(1, 4)
        ]
        + [
            (
                f"ablation_experiment_results/22_exp4_test_split_4o_prompt2/checkpoints/22_exp4_test_split_4o_prompt2_{i}/json_logs/",
                f"exp4_4o_run{i}",
            )
            for i in range(1, 4)
        ]
        + [
            (
                f"ablation_experiment_results/22_exp4_test_split_o3mini/run{i}/checkpoints/22_exp4_test_split_o3mini_{i}/json_logs/",
                f"exp4_o3mini_run{i}",
            )
            for i in range(1, 4)
        ]
        + [
            (
                f"ablation_experiment_results/20_exp1_test/run{i}/checkpoints/20_exp1_test_{i}/json_logs/",
                f"exp1_4omini_run{i}",
            )
            for i in range(1, 4)
        ] +
        [
            (
                f"ablation_experiment_results_arr_sept/full_test/lp/full_re1_exp4_Meta-Llama-3.1-8B-Instruct_idx{i-1}/json_logs/",
                f"llama3.1_full_run{i}",
            )
            for i in range(1, 4)
        ] + 
        [
            (
                f"ablation_experiment_results_arr_sept/10_perc_test/lp_qwen/re1_exp4_qwen3_14B_Qwen3-14B_idx{i-1}/json_logs/",
                f"qwen3_10perc_run{i}",
            )
            for i in range(1, 4)
        ]
    ):
        main(results_path=input_path, results_name=name)

