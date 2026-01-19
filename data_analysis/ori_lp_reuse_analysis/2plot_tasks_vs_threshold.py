"""Try to plot soft reuse?
"""

import json
import os
import matplotlib.pyplot as plt
plt.rcParams["font.family"] = "serif"
import numpy as np


def plot_amort(amort_path, key, color, line_args, dev=False, ax=None):
    if ax is None:
        ax = plt.gca()

    with open(amort_path, "r") as infile:
        data = json.load(infile)
        print(data)

    task_with_reuse_count = np.array(data[key])
    totals = np.array(data["num_successes"])
    thresholds = data["thresholds"]

    if dev:
        # Percentage of solved tasks
        means = (
            (task_with_reuse_count / totals[:, np.newaxis] * 100).mean(axis=0).flatten()
        )
        stds = (
            (task_with_reuse_count / totals[:, np.newaxis] * 100)
            .std(axis=0, ddof=1)
            .flatten()
        )

        ax.plot(thresholds, means, color=color, **line_args)
        ax.fill_between(thresholds, means - stds, means + stds, alpha=0.2, color=color)

    else:
        total_sums = task_with_reuse_count.flatten() #task_with_reuse_count.sum(axis=0).flatten()
        ax.plot(thresholds, total_sums, color=color, **line_args)


def generate_plot(amort_reuse1, outpath, title):
    plot_amort(
        amort_reuse1, "task_with_use_count", color="blue", line_args={"linestyle": "-", "label": "Uses Lemma"}
    )
    plot_amort(
        amort_reuse1, "task_with_reuse_count",
        color="orange",
        line_args={"linestyle": "--", "label": "Reuses Lemma"},
    )
    plt.title(title)
    plt.xlabel("Similarity Threshold")
    plt.ylabel("Number of Tasks Exhibiting Use")
    ax = plt.gca()
    ax.axhline(0, color="red", linestyle="-")
    plt.legend()

    plt.savefig(outpath)
    plt.close()

def main():
    from pathlib import Path
    OUTDIR = Path("data_analysis/ori_lp_reuse_analysis/lego_result")
    os.makedirs(OUTDIR, exist_ok=True)

    EXTENSION = "png" #"pdf"
    SPLITS = ['gpt_informal_test.json', 'gpt_informal_valid.json', 'human_informal_test.json', 'human_informal_valid.json']

    INFO = [
        (OUTDIR/f'soft_sim_{x}', OUTDIR/f'plotted_{x}.{EXTENSION}', x) for x in SPLITS
    ]

    for amort_reuse1, outpath, title in INFO:
        generate_plot(amort_reuse1, outpath, title)

if __name__ == "__main__":
    main()
