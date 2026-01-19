"""
Generate the table of model accuracies, adjusting to reduce
the number of LP attempts so as to match DSP's budget.
"""

import pandas as pd
import numpy as np
from tabulate import tabulate

COSTS = {
    "o3-mini": {"in": 1.1, "out": 4.4},
    "gpt-4o": {"in": 2.5, "out": 10},
    "4o-mini": {"in": 0.15, "out": 0.60},
}


def get_cost(df, syst, llm):
    return (
        float(df[df["model"] == syst]["in_M"].to_numpy().sum()) * COSTS[llm]["in"]
        + float(df[df["model"] == syst]["out_M"].to_numpy().sum()) * COSTS[llm]["out"]
    )


if __name__ == "__main__":
    df_exp1 = pd.read_csv("data_analysis/exp1.csv")
    df_exp5_gpt4o = pd.read_csv("data_analysis/exp5_gpt4o.csv")
    df_exp4_gpt4o = pd.read_csv("data_analysis/exp4_gpt4o.csv")
    df_exp3_gpt4o = pd.read_csv("data_analysis/exp3_gpt4o.csv")
    df_exp3_o3 = pd.read_csv("data_analysis/exp3_o3_mini.csv")
    df_exp4_o3 = pd.read_csv("data_analysis/exp4_o3_mini.csv")

    df_cost_exp1 = pd.read_csv("data_analysis/exp1_tok_use.csv")
    df_cost_exp5_gpt4o = pd.read_csv("data_analysis/exp5_gpt4o_tok_use.csv")
    df_cost_exp4_gpt4o = pd.read_csv("data_analysis/exp4_gpt4o_tok_use.csv")
    df_cost_exp3_gpt4o = pd.read_csv("data_analysis/exp3_gpt4o_tok_use.csv")
    df_cost_exp3_o3 = pd.read_csv("data_analysis/exp3_o3_mini_tok_use.csv")
    df_cost_exp4_o3 = pd.read_csv("data_analysis/exp4_o3_mini_tok_use.csv")

    table = [
        [
            "",
            r"gpt-4o-mini\footnotemark[1]",
            r"gpt-4o\footnotemark[2]",
            r"gpt-4o\footnotemark[3]",
            r"gpt-4o\footnotemark[4]",
            r"o3-mini\footnotemark[3]",
            r"o3-mini\footnotemark[4]",
        ]
    ]

    lp_attempts = ["lp attempts"]

    for model in ["dsp", "lp"]:
        table.append([model])
        for df, df_cost, num_questions, llm, dsp_att in [
            (df_exp1, df_cost_exp1, 244, "4o-mini", 100),
            (df_exp5_gpt4o, df_cost_exp5_gpt4o, 49, "gpt-4o", 50),
            (df_exp4_gpt4o, df_cost_exp4_gpt4o, 24, "gpt-4o", 50),
            (df_exp3_gpt4o, df_cost_exp3_gpt4o, 12, "gpt-4o", 50),
            (df_exp4_o3, df_cost_exp4_o3, 24, "o3-mini", 50),
            (df_exp3_o3, df_cost_exp3_o3, 12, "o3-mini", 50),
        ]:
            if model == "lp":
                lp_cost = get_cost(df_cost, "lp", llm)
                dsp_cost = get_cost(df_cost, "dsp", llm)
                adj_lp_attempts = round(dsp_att * (dsp_cost / lp_cost))
                num_solved = (
                    df[
                        (df["model"] == model)
                        & (df["problem_attempt"] <= adj_lp_attempts)
                    ]
                    .groupby("run")["successful_problem"]
                    .count()
                )
                lp_attempts.append(adj_lp_attempts)
            else:
                num_solved = (
                    df[df["model"] == model]
                    .groupby("run")["successful_problem"]
                    .count()
                )
            accs = num_solved.to_numpy() / num_questions * 100
            table[-1].append(f"{accs.mean():.1f} $\\pm$ {accs.std(ddof=1):.1f}\\%")

    table.append(lp_attempts)
    print(tabulate(table, headers="firstrow", tablefmt="latex_raw"))
    print()
    print(r"\footnotesize{\footnotemark[1] 100 DSP attempts, miniF2F test set}\\ ")
    print(
        r"\footnotesize{\footnotemark[2] 50 DSP attempts, 20\% of miniF2F test set}\\ "
    )
    print(
        r"\footnotesize{\footnotemark[3] 50 DSP attempts, 10\% of miniF2F test set}\\ "
    )
    print(
        r"\footnotesize{\footnotemark[4] 50 DSP attempts, 5\% of miniF2F test set}\\ "
    )
