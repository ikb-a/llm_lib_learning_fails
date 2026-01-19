"""
Plotting utilities.
"""

import numpy as np
import os
import json
from tqdm import tqdm

# From azure page: retrieved Tue Mar 11, 2025
# https://azure.microsoft.com/en-us/pricing/details/cognitive-services/openai-service/
COSTS = {
    "o3-mini": {"in": 1.1, "out": 4.4},
    "gpt-4o": {"in": 2.5, "out": 10},
    "4o-mini": {"in": 0.15, "out": 0.60},
}

# We ignore the cost of Ada usage in LEGO-Prover
IGNORE_ADA = True

ada_cost = 0 if IGNORE_ADA else 0.0001  # 0.0001/ 1000 tokens


def calc_avg_attempt_cost(target_df, model, attempts, runs=None) -> float:
    """Return the average cost per attempt for <model>, assuming each run id
    performed <attempts> attempts.

    Assume target_df only contains relevant rows, each with in_M, out_M, and ada_K
    (token usage, input in millions, output in millions, and ada in thousands)
    """
    return _calc_avg_attempt_cost(
        _get_tok_usages(target_df), model, attempts, runs=runs
    )


# (tokens in (M), tokens out (M), ada (K)); note ADA reported in thousands, NOT millions
def _calc_avg_attempt_cost(
    token_usage: list[tuple[float, float, float]], model: str, attempts, runs=None
) -> float:
    # Cost per million input, output & ada tokens
    cost_per_M = np.array([[COSTS[model]["in"], COSTS[model]["out"], ada_cost]])

    # Determine total costs
    expenses = np.array(token_usage) * cost_per_M

    # Add and average by the total number of solver attempts that occurred
    # (note: we're simplifying and considering "attempt" to mean attempt on all remaining problems)
    return np.sum(expenses) / (attempts * (runs if runs else len(token_usage)))


def _get_tok_usages(target_df) -> list[tuple[float, float, float]]:
    """
    For the given dataframe corresponding to a .csv of token usages,
    return a list of (input tokens, output tokens, Ada tokens)
    tuples. Note that input and output tokens are in millions, whereas
    Ada tokens are in thousands.
    """
    results = []

    for row in target_df.itertuples():
        if row.ada_K == "TODO":
            print("WARNING WARNING WARNING: Setting unknown ADA usage to 0.")

        if "-" not in str(row.run):
            results.append(
                (row.in_M, row.out_M, float(row.ada_K) if row.ada_K != "TODO" else 0)
            )
        else:  # We recorded several runs at once, take the average
            start_run, end_run = str(row.run).split("-")
            start_run, end_run = int(start_run), int(end_run)
            assert end_run > start_run
            num_runs = end_run - start_run + 1
            for i in range(num_runs):
                results.append(
                    (
                        row.in_M / num_runs,
                        row.out_M / num_runs,
                        float(row.ada_K) / num_runs if row.ada_K != "TODO" else 0,
                    )
                )

    return results


# If the average cost per attempt is provided, then scale x axis accordingly
def plot_runs(
    plt,
    num_runs,
    runs,
    label,
    style,
    total_problems,
    max_y_test: int = 50,
    avg_attempt_cost: float | None = None,
    color=None,
):

    assert len(runs) == num_runs
    print(runs)
    x_tests = list(range(max_y_test + 1))
    y_tests = np.zeros((len(runs), max_y_test + 1))

    for j, run in enumerate(runs):
        y_tests[j] = np.array(
            list(
                len([i for i in run if i <= x]) / total_problems * 100 for x in x_tests
            )
        )

    y_tests_means = np.mean(y_tests, axis=0)
    y_tests_std = np.std(y_tests, axis=0)
    print(y_tests_means)
    print(y_tests_std)

    if avg_attempt_cost is not None:
        x_tests = np.array(x_tests)
        x_tests = x_tests * avg_attempt_cost

    plt.plot(x_tests, y_tests_means, label=label, linestyle=style, color=color)

    plt.fill_between(
        x_tests,
        y_tests_means - y_tests_std,
        y_tests_means + y_tests_std,
        alpha=0.5,
        color=color,
    )


def fails_blacklist(x: dict | str, blacklist: str) -> bool:
    """
    Returns whether the lemma x is in blacklist, a list
    of lemma strings
    """
    if isinstance(x, str):
        return x in blacklist
    else:
        return x["code"] in blacklist


def load_formalizer_free_lemmas(
    results_path: str | os.PathLike, silent: bool = False
) -> set[str]:
    all_lemmas = set()
    black_list = set()

    # Find out which problems were correctly solved
    solved_tasks = set()
    for attempt in tqdm(os.listdir(results_path), disable=silent):
        if not attempt.endswith(".json"):
            continue
        with open(os.path.join(results_path, attempt), "r") as infile:
            attempt_data = json.load(infile)

        if not attempt_data["success"]:
            continue
        solved_tasks.add(attempt_data["task"])
    print(f"{len(solved_tasks)} tasks solved")

    # Add all lemmas created by LP
    print("Load LP generated lemmas", flush=True)
    with open(
        os.path.join(results_path, "..", "skill", "provenance.json"), "r"
    ) as infile:
        provenance = json.load(infile)
    for entity in tqdm(provenance, disable=silent):
        assert entity["created_type"] in ("request", "skill"), entity
        if entity["created_type"] == "request":
            continue
        elif (
            entity["creating_process"] == "prover_formalizer"
            and entity["creating_task"] in solved_tasks
        ):
            black_list.add(entity["created_body"])
            continue
        elif any(fails_blacklist(x, black_list) for x in entity["inputs"]):
            black_list.add(entity["created_body"])
            continue

        all_lemmas.add(entity["created_body"])

    print(
        f"{len(black_list)} Lemmas black listed due to descending from prover formalizer"
    )

    # Add the human written starter lemmas
    print("Load human starter lemmas", flush=True)
    for filename in os.listdir("data/initialize_skills/skill/code/"):
        if not filename.endswith(".thy"):
            continue
        with open(
            os.path.join("data/initialize_skills/skill/code/", filename), "r"
        ) as infile:
            all_lemmas.add(infile.read())

    print(f"Done loading. {len(all_lemmas)} lemmas loaded.")
    return all_lemmas
