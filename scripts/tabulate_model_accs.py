"""
Generate the table of model accuracies.
"""

import pandas as pd
import numpy as np
from tabulate import tabulate

if __name__ == "__main__":
    df_exp1 = pd.read_csv("data_analysis/exp1.csv")
    df_exp5_gpt4o = pd.read_csv("data_analysis/exp5_gpt4o.csv")
    df_exp4_gpt4o = pd.read_csv("data_analysis/exp4_gpt4o.csv")
    df_exp3_gpt4o = pd.read_csv("data_analysis/exp3_gpt4o.csv")

    df_exp3_o3 = pd.read_csv("data_analysis/exp3_o3_mini.csv")
    df_exp4_o3 = pd.read_csv("data_analysis/exp4_o3_mini.csv")

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

    for model in ["dsp", "lp"]:
        table.append([model])
        for df, num_questions in [
            (df_exp1, 244),
            (df_exp5_gpt4o, 49),
            (df_exp4_gpt4o, 24),
            (df_exp3_gpt4o, 12),
            (df_exp4_o3, 24),
            (df_exp3_o3, 12),
        ]:
            num_solved = (
                df[df["model"] == model].groupby("run")["successful_problem"].count()
            )
            accs = num_solved.to_numpy() / num_questions * 100
            table[-1].append(f"{accs.mean():.1f} $\\pm$ {accs.std(ddof=1):.1f}\\%")

    print(tabulate(table, headers="firstrow", tablefmt="latex_raw"))
    print()
    print(r"\footnotesize{\footnotemark[1] 100 attempts, miniF2F test set}\\ ")
    print(r"\footnotesize{\footnotemark[2] 50 attempts, 20\% of miniF2F test set}\\ ")
    print(r"\footnotesize{\footnotemark[3] 50 attempts, 10\% of miniF2F test set}\\ ")
    print(r"\footnotesize{\footnotemark[4] 50 attempts, 5\% of miniF2F test set}\\ ")
