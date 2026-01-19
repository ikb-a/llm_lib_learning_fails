import json
import os
import matplotlib.pyplot as plt
plt.rcParams["font.family"] = "serif"
import numpy as np


def plot_use(thresholds, counts, color, line_args, ax, dev=False):
    if dev:
        means = (
            (np.array(counts) / np.array(counts)[:, 0, np.newaxis] * 100)
            .mean(axis=0)
            .flatten()
        )
        ax.plot(thresholds, means, color=color, **line_args)
        stds = (
            (np.array(counts) / np.array(counts)[:, 0, np.newaxis] * 100)
            .std(axis=0, ddof=1)
            .flatten()
        )
        ax.fill_between(
            x=thresholds, y1=means - stds, y2=means + stds, alpha=0.2, color=color
        )
    else:
        sums = np.array(counts).sum(axis=0)
        ax.plot(thresholds, sums, color=color, **line_args)


def plot_amort(amort_path, color_array, line_args_array, ax, dev=False):
    with open(amort_path, "r") as infile:
        data = json.load(infile)

    thresholds = data["thresholds"]
    reused_lemmas_count = data["reused_lemmas_count"]
    non_retr_count = data["non_retr_count"]
    unrelated_count = data["unrelated_count"]

    for count, col, arg in zip(
        [reused_lemmas_count, non_retr_count, unrelated_count],
        color_array,
        line_args_array,
    ):
        plot_use(thresholds, count, col, arg, ax, dev=dev)


def generate_plot(amort_reuse1, amort_reuse2, outpath, title):
    cols = ["blue", "red", "orange"]
    lins = [
        {"linestyle": "-", "label": "Retrieved Lemmas"},
        {"linestyle": "-", "label": "Non-Retrieved Lemmas"},
        {"linestyle": "-", "label": "Irrelevant AFP Lemmas"},
    ]

    fig, axes = plt.subplots(
        nrows=1, ncols=2, sharey=True, figsize=(10, 5)
    )  # , figsize=(5, 3))
    plot_amort(
        amort_reuse1, color_array=cols, line_args_array=lins, ax=axes[0], dev=True
    )

    for ln in lins:
        del ln["label"]

    plot_amort(
        amort_reuse2, color_array=cols, line_args_array=lins, ax=axes[1], dev=True
    )
    fig.suptitle(title)
    fig.supxlabel("Similarity Threshold for Use")
    axes[0].set_ylabel("% of Lemmas Matching >= 1 Solutions")
    axes[1].set_ylabel("% of Lemmas Matching >= 2 Solutions")
    ax = plt.gca()
    ax.axhline(0, color="red", linestyle="-")
    fig.legend()

    plt.savefig(outpath[:-4] + "_dev" + outpath[-4:])
    plt.close()


def main():
    OUTDIR = "data_analysis/calc_common_FINAL2_lemma_survival"
    os.makedirs(OUTDIR, exist_ok=True)
    AMORT_NAME1 = (
        "afp.json"  # 1-use results (i.e., tasks with single lemma meeting threshold)
    )
    AMORT_NAME2 = (
        "all_afp.json"  # 2-reuse results (i.e., tasks with 2 lemmas meeting threshold)
    )
    EXTENSION = "png"

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
    fig, axes = plt.subplots(nrows=2, ncols=5, figsize=(9.5, 4), sharey=True)#(8, 4)

    MARGIN_BOT = 0
    MARGIN_TOP = 1
    plt.ylim((0 - MARGIN_BOT, 100 + MARGIN_TOP))

    cols = ["blue", "red", "orange"]
    lins = [
        {"linestyle": "-", "label": "Retrieved Lemmas"},
        {"linestyle": "--", "label": "Non-Retrieved Lemmas"},
        {"linestyle": "-.", "label": "Irrelevant AFP Lemmas"},
    ]

    for i, ((amort_reuse1, amort_reuse2, outpath, title), ax_top, ax_bot) in enumerate(
        zip(INFO, axes[0], axes[1])
    ):
        title = f"{title}"
        plot_amort(
            amort_reuse1, color_array=cols, line_args_array=lins, ax=ax_top, dev=True
        )
        if i == 0:
            fig.legend(loc=(0.7, 0.65))  # x,y
            ax_top.set_ylabel("% of Lemmas\nSoft Used\n(Matching \n≥ 1 Solutions)")
            ax_bot.set_ylabel("% of Lemmas\nSoft Reused\n(Matching \n≥ 2 Solutions)")
        plot_amort(
            amort_reuse2, color_array=cols, line_args_array=lins, ax=ax_bot, dev=True
        )

        ax_top.set_title(title)

    fig.subplots_adjust(bottom=0.17)
    fig.subplots_adjust(left=0.15)
    fig.supxlabel(
        "Similarity Threshold for Soft Use & Reuse\n(0 is any degree of use and 1 is direct use)"
    )

    plt.suptitle("Proportion of Lemmas Satisfying Soft Use or Reuse Similarity in Solved LEGO-Prover Tasks", y=0.95)
    plt.tight_layout()

    plt.savefig(os.path.join(OUTDIR, f"lemma_surv.{EXTENSION}"))
    plt.savefig(os.path.join(OUTDIR, f"lemma_surv.pdf"))


if __name__ == "__main__":
    main()
