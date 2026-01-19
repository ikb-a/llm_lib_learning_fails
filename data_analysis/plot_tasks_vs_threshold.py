import json
import os
import matplotlib.pyplot as plt
plt.rcParams["font.family"] = "serif"
import numpy as np


def plot_amort(amort_path, color, line_args, dev=False, ax=None):
    if ax is None:
        ax = plt.gca()

    with open(amort_path, "r") as infile:
        data = json.load(infile)

    task_with_reuse_count = np.array(data["task_with_reuse_count"])
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
        total_sums = task_with_reuse_count.sum(axis=0).flatten()
        ax.plot(thresholds, total_sums, color=color, **line_args)


def generate_plot(amort_reuse1, amort_reuse2, outpath, title):
    plot_amort(
        amort_reuse1, color="blue", line_args={"linestyle": "-", "label": "Uses Lemma"}
    )
    plot_amort(
        amort_reuse2,
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

    plot_amort(
        amort_reuse1,
        color="blue",
        line_args={"linestyle": "-", "label": "Uses Lemma"},
        dev=True,
    )
    plot_amort(
        amort_reuse2,
        color="orange",
        line_args={"linestyle": "--", "label": "Reuses Lemma"},
        dev=True,
    )
    plt.title(title)
    plt.xlabel("Similarity Threshold for Use")
    plt.ylabel("Percentage of Solved Tasks Meeting Criteria")
    ax = plt.gca()
    ax.axhline(0, color="red", linestyle="-")
    plt.legend()

    plt.savefig(outpath[:-4] + "_dev" + outpath[-4:])
    plt.close()


def main():
    OUTDIR = "data_analysis/calc_common_FINAL1_task_vs_threshold"
    os.makedirs(OUTDIR, exist_ok=True)
    AMORT_NAME1 = (
        "afp.json"  # 1-use results (i.e., tasks with single lemma meeting threshold)
    )
    AMORT_NAME2 = (
        "all_afp.json"  # 2-reuse results (i.e., tasks with 2 lemmas meeting threshold)
    )
    EXTENSION = "png"  # "pdf"

    INFO = [
        (
            os.path.join(
                "data_analysis/calc_common_ancestors_ONE_TASK/exp1_4omini/", AMORT_NAME1
            ),
            os.path.join(
                "data_analysis/calc_common_ancestors/exp1_4omini/", AMORT_NAME2
            ),
            os.path.join(OUTDIR, f"exp1_4omini.{EXTENSION}"),
            "4o-mini",
        ),
        (
            os.path.join(
                "data_analysis/calc_common_ancestors_ONE_TASK/100perc_llama3.1/", AMORT_NAME1
            ),
            os.path.join(
                "data_analysis/calc_common_ancestors/100perc_llama3.1/", AMORT_NAME2
            ),
            os.path.join(OUTDIR, f"100percent_llama3.1.{EXTENSION}"),
            "Llama3.1-8B",
        ),
        (
            os.path.join(
                "data_analysis/calc_common_ancestors_ONE_TASK/exp5_4o/", AMORT_NAME1
            ),
            os.path.join("data_analysis/calc_common_ancestors/exp5_4o/", AMORT_NAME2),
            os.path.join(OUTDIR, f"exp5_4o.{EXTENSION}"),
            "4o",
        ),
        (
            os.path.join(
                "data_analysis/calc_common_ancestors_ONE_TASK/exp4_o3mini/", AMORT_NAME1
            ),
            os.path.join(
                "data_analysis/calc_common_ancestors/exp4_o3mini/", AMORT_NAME2
            ),
            os.path.join(OUTDIR, f"exp4_o3mini.{EXTENSION}"),
            "o3-mini",
        ),
        (
            os.path.join(
                "data_analysis/calc_common_ancestors_ONE_TASK/10perc_qwen3/", AMORT_NAME1
            ),
            os.path.join(
                "data_analysis/calc_common_ancestors/10perc_qwen3/", AMORT_NAME2
            ),
            os.path.join(OUTDIR, f"10percent_qwen3.{EXTENSION}"),
            "Qwen3-14B",
        ),
    ]

    for amort_reuse1, amort_reuse2, outpath, title in INFO:
        generate_plot(amort_reuse1, amort_reuse2, outpath, title)

    # Create joint plot
    fig, axes = plt.subplots(nrows=1, ncols=5, figsize=(9.5, 4), sharey=True)

    MARGIN_BOT = 0
    MARGIN_TOP = 1
    plt.ylim((0 - MARGIN_BOT, 100 + MARGIN_TOP))

    for i, ((amort_reuse1, amort_reuse2, outpath, title), ax) in enumerate(
        zip(INFO, axes)
    ):
        title = f"{title}"
        plot_amort(
            amort_reuse1,
            color="blue",
            line_args={"linestyle": "-", "label": "Soft Use \nof Lemma"},
            dev=True,
            ax=ax,
        )
        plot_amort(
            amort_reuse2,
            color="orange",
            line_args={"linestyle": "--", "label": "Soft Reuse \nof Lemma"},
            dev=True,
            ax=ax,
        )
        ax.set_title(title)
        if i == 0:
            fig.legend(loc=(0.8, 0.6))  # x,y  loc=(0.8,0.6))#

    fig.subplots_adjust(bottom=0.16)
    fig.supxlabel(
        "Similarity Threshold for Soft Use & Reuse\n(0 is any degree of use and 1 is direct use)",
        y=0,
    )
    fig.supylabel(
        "Percentage of Tasks Exhibiting \nSoft Use/Reuse", multialignment="center"
    )

    plt.suptitle("Soft Use and Soft Reuse in Solved LEGO-Prover Tasks", y=0.95)
    plt.tight_layout()
    plt.savefig(os.path.join(OUTDIR, f"task_surv.{EXTENSION}"))
    plt.savefig(os.path.join(OUTDIR, f"task_surv.png"))


if __name__ == "__main__":
    main()
