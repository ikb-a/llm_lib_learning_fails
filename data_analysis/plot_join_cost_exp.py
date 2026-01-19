"""
Plot all of our cost-adjusted experiments, stacked on top of eachother
"""

import pandas as pd
#from data_analysis.plot_utils import calc_avg_attempt_cost, plot_runs
import matplotlib.pyplot as plt
plt.rcParams["font.family"] = "serif"
import os

#import sys
#sys.path.append("/home/ianberlo/initiatives/Lego-Prover")

import numpy as np


# From azure page: retrieved Tue Mar 11, 2025
# https://azure.microsoft.com/en-us/pricing/details/cognitive-services/openai-service/
# COSTS = {
#     "o3-mini": {"in": 1.1, "out": 4.4},
#     "gpt-4o": {"in": 2.5, "out": 10},
#     "4o-mini": {"in": 0.15, "out": 0.60},
#     "Llama3.1-8B": {"in": 10**6, "out": 10**6},
#     "Qwen3-14B": {"in": 10**6, "out": 10**6},
# }

from collections import defaultdict
COSTS = defaultdict(lambda: {"in": 1, "out": 1})

# We ignore the cost of Ada usage in LEGO-Prover
IGNORE_ADA = True

ada_cost = 0 if IGNORE_ADA else 0.0001  # 0.0001/ 1000 tokens

DSP_COL = "blue"
LP_COL = "orange"

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


def calc_avg_attempt_cost(target_df, model, attempts, runs=None) -> float:
    """Return the average cost per attempt for <model>, assuming each run id
    performed <attempts> attempts.

    Assume target_df only contains relevant rows, each with in_M, out_M, and ada_K
    (token usage, input in millions, output in millions, and ada in thousands)
    """
    return _calc_avg_attempt_cost(
        _get_tok_usages(target_df), model, attempts, runs=runs
    )



def _get_tok_usages(target_df) -> list[tuple[float, float, float]]:
    """
    For the given dataframe corresponding to a .csv of token usages,
    return a list of (input tokens, output tokens, Ada tokens)
    tuples. Note that input and output tokens are in millions, whereas
    Ada tokens are in thousands.
    """
    results = []

    for row in target_df.itertuples():
        zero_ada = ["TODO", 'UNRECORDED']
        if row.ada_K in zero_ada:
            print("WARNING WARNING WARNING: Setting unknown ADA usage to 0.")

        if "-" not in str(row.run):
            results.append(
                (row.in_M, row.out_M, float(row.ada_K) if row.ada_K not in zero_ada else 0)
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


def my_filter(df, model, dataset):
    return df[(df["model"] == model) & (df["dataset"] == dataset)]


def get_transitions(df, model, dataset, runs=3) -> list[list[int]]:
    """
    Generate list of runs.
    Each run in turn is represented by a list of timesteps at which it solved a problem.
    """
    df = df[(df["model"] == model) & (df["dataset"] == dataset)]
    return [
        sorted(df[df["run"] == run]["problem_attempt"].tolist())
        for run in range(1, runs + 1)
    ]


def plot_lp_from_csv(
    lp_df,
    lp_tok_use_df,
    dataset,
    ax,
    total_problems,
    llm,
    attempts=50,
    runs=3,
    plot_line_label="LEGO-Prover",
):
    lp_df = pd.read_csv(lp_df)
    lp_tok_use_df = pd.read_csv(lp_tok_use_df)

    plot_runs(
        ax,
        runs,
        get_transitions(lp_df, "lp", dataset),
        plot_line_label,
        "-",
        total_problems=total_problems,
        max_y_test=attempts,
        avg_attempt_cost=calc_avg_attempt_cost(
            my_filter(lp_tok_use_df, "lp", dataset), llm, attempts=attempts
        ),
        color=LP_COL,
    )


def plot_dsp_from_csv(
    dsp_df,
    dsp_tok_use_df,
    dataset,
    ax,
    total_problems,
    llm,
    attempts,
    ori_dsp_attempts=50,
    plot_line_label="DSP",
    runs=3,
):
    dsp_df = pd.read_csv(dsp_df)
    dsp_tok_use_df = pd.read_csv(dsp_tok_use_df)

    assert attempts >= 50
    avg_attempt_cost = calc_avg_attempt_cost(
        my_filter(dsp_tok_use_df, "dsp", dataset), llm, attempts=attempts, runs=runs
    )
    plot_runs(
        ax,
        runs,
        get_transitions(dsp_df, "dsp", dataset),
        plot_line_label,
        "--",
        total_problems=total_problems,
        max_y_test=attempts,
        avg_attempt_cost=avg_attempt_cost,
        color=DSP_COL,
    )

    ax.axvline(ori_dsp_attempts * avg_attempt_cost, linestyle="--", color=DSP_COL)


def main():
    fig, axes = plt.subplots(nrows=5, ncols=1, figsize=(3.5, 6))  # , figsize=(5, 3))#(7, 8)

    fig.suptitle("LP and DSP Accuracy vs. Avg. Cost")
    fig.supxlabel("Avg. Cost (Total Tokens in Millions)")
    fig.supylabel("% of Tasks Solved")

    
    # Qwen results
    plot_lp_from_csv(
        lp_df="data_analysis/qwen3_lp_10perc.csv",
        lp_tok_use_df="data_analysis/qwen3_lp_10perc_token.csv",
        dataset="test24",
        ax=axes[4],
        total_problems=24,
        llm="Qwen3-14B",
        attempts=50,
        runs=3,
    )
    plot_dsp_from_csv(
        dsp_df="data_analysis/qwen3_dsp_10prec.csv",
        dsp_tok_use_df="data_analysis/qwen3_dsp_10prec_token.csv",
        dataset="test24",
        ax=axes[4],
        total_problems=24,
        llm="Qwen3-14B",
        attempts=300,
        ori_dsp_attempts=50,
        runs=3,
    )
    axes[4].set_ylabel("Qwen3-14B\n10% Test Set", multialignment="center")


    #fig.legend(loc='lower right')
    axes[4].legend(loc='lower right', borderaxespad=0, fontsize=10, markerscale=0.5, handlelength=1, handletextpad=0.5) # bbox_to_anchor=(1, 0.9), 

# Experiment 1:
    plot_lp_from_csv(
        lp_df="data_analysis/exp1.csv",
        lp_tok_use_df="data_analysis/exp1_tok_use.csv",
        dataset="test",
        ax=axes[0],
        total_problems=244,
        llm="4o-mini",
        attempts=100,
        runs=3,
    )

    plot_dsp_from_csv(
        dsp_df="data_analysis/exp1.csv",
        dsp_tok_use_df="data_analysis/exp1_tok_use.csv",
        dataset="test",
        ax=axes[0],
        total_problems=244,
        llm="4o-mini",
        attempts=100,
        ori_dsp_attempts=100,
        runs=3,
    )
    axes[0].set_ylabel("4o-mini\n100% Test Set", multialignment="center")

    # Experiment 4b o3-mini:
    plot_lp_from_csv(
        lp_df="data_analysis/exp4_o3_mini.csv",
        lp_tok_use_df="data_analysis/exp4_o3_mini_tok_use.csv",
        dataset="test24",
        ax=axes[1],
        total_problems=24,
        llm="o3-mini",
        attempts=50,
        runs=3,
    )

    plot_dsp_from_csv(
        dsp_df="data_analysis/exp4b_o3_mini.csv",
        dsp_tok_use_df="data_analysis/exp4b_o3_mini_tok_use.csv",
        dataset="test24",
        ax=axes[1],
        total_problems=24,
        llm="o3-mini",
        attempts=250,
        ori_dsp_attempts=50,
        runs=3,
    )
    axes[1].set_ylabel("o3-mini\n10% Test Set", multialignment="center")
    
    # 10% Llama 3.1
    """
    plot_lp_from_csv(
        lp_df="data_analysis/llama3.1_10perc.csv",
        lp_tok_use_df="data_analysis/llama3.1_10perc_token.csv",
        dataset="test24",
        ax=axes[2],
        total_problems=24,
        llm="Llama3.1-8B",
        attempts=50,
        runs=3,
    )
    plot_dsp_from_csv(
        dsp_df="data_analysis/llama3.1_10perc.csv",
        dsp_tok_use_df="data_analysis/llama3.1_10perc_token.csv",
        dataset="test24",
        ax=axes[2],
        total_problems=24,
        llm="Llama3.1-8B",
        attempts=300,
        ori_dsp_attempts=50,
        runs=3,
    )
    axes[2].set_ylabel("gpt-4o\n10% Test Set", multialignment="center")
    """

    #100% llama3.1
    plot_lp_from_csv(
        lp_df="data_analysis/llama3.1_full_lp.csv",
        lp_tok_use_df="data_analysis/llama3.1_full_lp_token.csv",
        dataset="test",
        ax=axes[2],
        total_problems=244,
        llm="Llama3.1-8B",
        attempts=50,
        runs=3,
    )
    plot_dsp_from_csv(
        dsp_df="data_analysis/llama3.1_full_dsp_232atts_premature.csv",
        dsp_tok_use_df="data_analysis/llama3.1_full_dsp_232atts_premature_token.csv",
        dataset="test",
        ax=axes[2],
        total_problems=244,
        llm="Llama3.1-8B",
        attempts=232, # Iterations completed within available time
        ori_dsp_attempts=50,
        runs=3,
    )
    axes[2].set_ylabel("Llama3.1-8B\n100% Test Set", multialignment="center")


    # Experiment 5b 4o
    plot_lp_from_csv(
        lp_df="data_analysis/exp5_gpt4o.csv",
        lp_tok_use_df="data_analysis/exp5_gpt4o_tok_use.csv",
        dataset="test49",
        ax=axes[3],
        total_problems=49,
        llm="gpt-4o",
        attempts=50,
        runs=3,
    )

    plot_dsp_from_csv(
        dsp_df="data_analysis/exp5b_gpt4o.csv",
        dsp_tok_use_df="data_analysis/exp5b_gpt4o_tok_use.csv",
        dataset="test49",
        ax=axes[3],
        total_problems=49,
        llm="gpt-4o",
        attempts=250,
        ori_dsp_attempts=50,
        runs=3,
    )
    axes[3].set_ylabel("gpt-4o\n20% Test Set", multialignment="center")



    os.makedirs("data_analysis/plot_FINAL1_cost", exist_ok=True)
    plt.tight_layout()
    plt.savefig("data_analysis/plot_FINAL1_cost/all_costs.png")


if __name__ == "__main__":
    main()
