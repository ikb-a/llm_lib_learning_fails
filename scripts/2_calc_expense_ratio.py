"""
Calculate how many times more expensive 50 LP attempts are 
compared to 50 DSP attempts with the same LLM.

Script Output:

----------
o3-mini
14.228284728755098
----------
gpt-4o
5.941928938735834
----------
4o-mini
5.842473138213937
==========
8.434801660021225
"""

import pandas as pd

# From azure page: retrieved Tue Mar 11, 2025
# https://azure.microsoft.com/en-us/pricing/details/cognitive-services/openai-service/
COSTS = {
    "o3-mini": {"in": 1.1, "out": 4.4},
    "gpt-4o": {"in": 2.5, "out": 10},
    "4o-mini": {"in": 0.15, "out": 0.60},
}

# We chose to ignore the cost of Ada embeddings in LEGO-Prover as we were unable
# to collect the token usage for all LEGO-Prover runs. Note that for the
# runs where we collected this information,  we found the cost to
# be negligible compared to token usage by the main underlying LLM.
IGNORE_ADA = True
ada_cost = 0 if IGNORE_ADA else 0.0001  # 0.0001/ 1000 tokens

DATA = {
    "o3-mini": [
        pd.read_csv(
            "data_analysis/exp3_o3_mini_tok_use.csv",
        ),
        pd.read_csv(
            "data_analysis/exp4_o3_mini_tok_use.csv",
        ),
    ],
    "gpt-4o": [
        pd.read_csv(
            "data_analysis/exp4_gpt4o_tok_use.csv",
        ),
        pd.read_csv(
            "data_analysis/exp3_gpt4o_tok_use.csv",
        ),
        pd.read_csv(
            "data_analysis/exp5_gpt4o_tok_use.csv",
        ),
    ],
    "4o-mini": [
        pd.read_csv(
            "data_analysis/exp1_tok_use.csv",
        ),
        pd.read_csv(
            "data_analysis/exp2_tok_use.csv",
        ),
    ],
}

if __name__ == "__main__":
    total_dsp = 0
    total_lp = 0
    for model in DATA:
        model_dsp_cost = 0
        model_lp_cost = 0
        for df in DATA[model]:
            model_dsp_cost += (
                float(df[df["model"] == "dsp"]["in_M"].to_numpy().sum())
                * COSTS[model]["in"]
            )
            model_dsp_cost += (
                float(df[df["model"] == "dsp"]["out_M"].to_numpy().sum())
                * COSTS[model]["out"]
            )

            model_lp_cost += (
                float(df[df["model"] == "lp"]["in_M"].to_numpy().sum())
                * COSTS[model]["in"]
            )
            model_lp_cost += (
                float(df[df["model"] == "lp"]["out_M"].to_numpy().sum())
                * COSTS[model]["out"]
            )

        print("-" * 10)
        print(model)
        total_dsp += model_dsp_cost
        total_lp += model_lp_cost
        print(model_lp_cost / model_dsp_cost)

    print("=" * 10)
    print(total_lp / total_dsp)
