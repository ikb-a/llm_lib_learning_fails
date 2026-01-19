"""
Calculate Max Potential Gain and Loss in the prompt
stability experiments.
"""

from tabulate import tabulate
from numpy import std as np_std
import pandas as pd


def avg(x):
    return sum(x) / len(x)


def std(x):
    return np_std(x, ddof=1)


TOTAL = 12  # Total number of problems

datasets = ["test12", "val12"]
prompts = ["baseline", "paraphrase"]


def fmt(x):
    x = [y / TOTAL * 100 for y in x]
    return f"${avg(x):.1f}\\pm {std(x):.1f}$\\%"


# From the paper originally defining Max potential gain:
"""
In Table 8, we show how the median is
calculated per example. For each example in a
task dataset, we take the downstream task scores
of paraphrased prompts that are higher than the
original prompt and take the median. Then, for all
examples in the dataset, we average that median.
Further, one can also compute the maximum per-
formance that can be reached
"""
# 0% improvement if same performance or worse, 100% if solved previously unsolved.
# Average over all 12 problems (i.e., becomes the fraction of problems that are
# newly solvable)
# Loss is reversed(0% if same, 100% if no longer solved) -- becomes fraction
# of problems that are no longer solved


def create_table(df, split, label):
    table = []

    # only interested in this dataset
    df = df[df["dataset"] == split]

    for model in ["dsp", "lp"]:
        row = [
            model,
        ]

        solved_problems = {}

        for prompt in ["baseline", "paraphrase"]:
            target_df = df[(df["model"] == model) & (df["prompt"] == prompt)]
            counts = target_df.groupby(
                "run"
            ).count()  # Count how many problems each run solved
            success_per_run = counts["successful_problem"].tolist()
            row.append(fmt(success_per_run))

            solved_problems[prompt] = set(target_df["successful_problem"].tolist())

        # Max Pot. Gain
        row.append(
            f"{len(solved_problems['paraphrase'] - solved_problems['baseline'])/TOTAL*100:.1f}\\%"
        )

        # Max Pot. Loss
        row.append(
            f"{len(solved_problems['baseline'] - solved_problems['paraphrase'])/TOTAL*100:.1f}\\%"
        )

        table.append(row)
    print(
        tabulate(
            headers=[
                "model",
                f"{label} Baseline acc",
                f"{label} Paraphrase acc",
                "Max Pot. Gain",
                "Max Pot. Loss",
            ],
            tabular_data=table,
            tablefmt="latex_raw",
        )
    )


if __name__ == "__main__":
    df = pd.read_csv("data_analysis/exp2.csv")
    for dataset in ["val12", "test12"]:
        create_table(df, dataset, dataset[:-2])
