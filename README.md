# LLM Library Learning Fails: A LEGO-Prover Case Study
## LEGO-Prover Experiments


[![Python Version](https://img.shields.io/badge/Python-3.10.12-blue.svg)](https://github.com/wiio12/LEGO-Prover)
[![GitHub license](https://img.shields.io/github/license/MineDojo/Voyager)](hhttps://github.com/wiio12/LEGO-Prover/blob/main/LICENSE)
[![Code style: black](https://img.shields.io/badge/code%20style-black-000000.svg)](https://github.com/psf/black)

This directory contains the code for reproducing the LEGO-Prover experiments performed in the paper LLM Library Learning Fails: A LEGO-Prover Case Study.

# Installation

This code is only tested under Python 3.10.12, on Ubuntu 18.04.

## Python Install
You should begin by cloning the project to local directory. Next, set up the environment:

```shell
python3.10 -m venv env
source env/bin/activate
pip install -e . 
pip install -r requirements_new2.txt
pip install protobuf==3.20.3
pip install openai==1.65.4
```
**Note:** pip might give error about incompatible versions for `protobuf`, `grpcio-tools`, but it works. Likewise, there will be pip warnings about lego-prover's requirements being incompatible with the installed packages; ignore these errors also.


## PISA Install
[PISA](https://github.com/albertqjiang/Portal-to-ISAbelle) (Portal to ISAbelle) is a REPL wrapper for Isabelle theorem prover. LEGO-Prover utilize PISA to communicate with Isabelle theorem prover and verify the formal code. You should follow the instruction bellow to install PISA and Isabelle. Note that we've already modified the copy of PISA in this directory to use a 120s timeout (See [this DSP issue](https://github.com/albertqjiang/draft_sketch_prove/issues/3) for details).

Note that while installing and configuring Isabell is required, it may not be necesary to compile PISA. We have provided our [PISA-assembly-120s-0.1.jar](lego_prover/env/Portal-to-ISAbelle/target/scala-2.13/PISA-assembly-120s-0.1.jar) which should operate cross-platform, though we cannot guarantee this.

1. **Scala configuration**
   
    Install SDKMAN
    ```shell
    cd ~
    curl -s "https://get.sdkman.io" | bash
    source .bashrc
    ```
    
    Install JAVA 11 and sbt
    ```shell
    sdk install java 11.0.11-open
    sdk install sbt
    ```

2. **Configure Isabelle**
    ```shell
    wget https://isabelle.in.tum.de/website-Isabelle2022/dist/Isabelle2022_linux.tar.gz
    tar -xzf Isabelle2022_linux.tar.gz
    export PATH="$PATH:$HOME/Isabelle2022/bin/"
    ```
    Try
    ```shell
    isabelle 
    ```
    to makes sure isabelle is properly installed.

3. **Compile PISA**

    ```shell
    cd lego_prover/env/Portal-to-ISAbelle
    sbt assembly
    ```
    Note that PISA can be very finicky.

4. **Rename**

    Rename the created file from 'PISA-assembly-0.1.jar' to 'PISA-assembly-120s-0.1.jar'; do not change the directory location.

## OpenAI API Keys
This project require Azure API Keys to properly query the OpenAI LLMs. LEGO-Prover always requires text-embedding-ada-002. It will also require one of gpt-4o-mini, gpt-4o, or o3-mini. Please make sure the API key provided have access to these models.

Please place your Azure API key in the `azure_keys.py` file.

# Evaluation
Example commands for running the LEGO-Prover are provided in the following sections. In all cases, the log will be stored in the `log` directory, the checkpoints will be stored in the `checkpoints/{NAME}` directory, and the performance will be printed to stdout (captured to `log.out`).

**Note**: the Isabelle formal verifier requires enormous cpu memories and computations, so keeps the number of parallel process low if you don't have a beefy machine.

Our experiments were run on 50CPU cores and 180GB of RAM.


## GPT-4o-mini Experiments

```shell
RUN=1  # Set to 1,2,3... for different runs

# Run on test set
python run_multiprocess.py --max_calls_per_s '-1' \
    --max_duration 24 \
    --data_split 'test' \
    --ckpt_dir "checkpoints/20_exp1_test_${RUN}/" \
    --num_attempts '100' \
    --num_prover 3 --num_evolver 8 --resume > log.out
```

## GPT-4o Experiments

```shell
RUN=1  # Set to 1,2,3... for different runs

# Run on 20% split of test set
python run_multiprocess.py --model_name 'gpt-4o' \
    --decomposer_prompt "Experiment3/gpt4o/decomposer_prompt2"  \
    --max_calls_per_s '-1' --max_duration 23 \
    --data_split 'custom/test_rand_20' \
    --ckpt_dir "checkpoints/21_exp5_test_split_4o_prompt2_${RUN}/" \
    --num_attempts '50' --num_prover 3 --num_evolver 8 > log.out

# Run on 10% split of test set
python run_multiprocess.py --model_name 'gpt-4o' \
    --decomposer_prompt "Experiment3/gpt4o/decomposer_prompt2" \
    --max_calls_per_s '-1' \
    --max_duration 23 \
    --data_split 'custom/test_rand_10' \
    --ckpt_dir "checkpoints/22_exp4_test_split_4o_prompt2_${RUN}/" \
    --num_attempts '50' --num_prover 3 --num_evolver 8 > log.out

# Run on 5% split of test set
python run_multiprocess.py --model_name 'gpt-4o' \
    --decomposer_prompt "Experiment3/gpt4o/decomposer_prompt2" \
    --max_calls_per_s '-1' \
    --max_duration 90 \
    --data_split 'custom/test_rand' \
    --ckpt_dir "checkpoints/17d_exp3_test_split_4o_prompt2_${RUN}/" \
    --num_attempts '50' --num_prover 3 --num_evolver 8 > log.out
```

## o3-mini Experiments

```shell
RUN=1  # Set to 1,2,3... for different runs

# Run on 10% split of test set
python run_multiprocess.py --model_name 'o3-mini' \
    --max_calls_per_s '-1' --max_duration 11.5 \
    --data_split 'custom/test_rand_10' \
    --ckpt_dir "checkpoints/22b_exp4_test_split_o3mini_prompt2_${RUN}/" \
    --num_attempts '50' --num_prover 3 --num_evolver 8 \
    --evolve_prompts 'lego_prover/prompts/Experiment3/o3mini/skill_evolver_o3mini_v4' \
    --formalizer_prompt 'Experiment3/o3mini/formalizer' \
    --decomposer_prompt 'Experiment3/o3mini/decomposer' > log.out

# Run on 5% split of test set
python run_multiprocess.py  \
    --model_name 'o3-mini' \
    --max_calls_per_s '-1' --max_duration 90 --data_split 'custom/test_rand' \
    --ckpt_dir "checkpoints/17b_exp3_test_split_o3mini_${RUN}/" \
    --num_attempts '50' --num_prover 3 --num_evolver 8 \
    --port_offset 24 \
    --evolve_prompts 'lego_prover/prompts/Experiment3/o3mini/skill_evolver_o3mini_v4' \
    --formalizer_prompt 'Experiment3/o3mini/formalizer' \
    --decomposer_prompt 'Experiment3/o3mini/decomposer'

```

## Prompt Stability Experiments

```shell
RUN=1  # Set to 1,2,3... for different runs

# Baseline prompt.
python run_multiprocess.py --max_calls_per_s '-1' \
    --max_duration 90 \
    --data_split 'custom/valid_rand' \
    --ckpt_dir "checkpoints/15d_prompt_stab_val_baseline_${RUN}/" \
    --num_attempts '50' --num_prover 3 --num_evolver 8 > log.out


# Paraphrased Prompts.
python run_multiprocess.py \
    --decomposer_prompt "paraphrases/decomposer1_${RUN}" \
    --formalizer_prompt "paraphrases/formalizer1_${RUN}" \
    --max_calls_per_s '-1' \
    --max_duration 90 \
    --data_split 'custom/valid_rand' \
    --ckpt_dir "checkpoints/15_prompt_stability_${RUN}/" \
    --num_attempts '50' --num_prover 3 --num_evolver 8 > log.out
```


# Data Analysis

Our direct re-use experiments can be run with [direct_reuse_analysis.py](data_analysis/direct_reuse_analysis.py).
We provide the script output at [direct_reuse_analysis.txt](data_analysis/direct_reuse_analysis.txt).
A subset of Lemmas exhibiting direct reuse (either verbatim or name match) are automatically saved to [direct_reuse](data_analysis/direct_reuse). Note that the filename prefix is the number of uses (i.e., one more than the number of reuses). The lemmas with the highest use are saved. If there are no lemmas exhibiting direct use, then the directory is empty.

To generate the lemma and task survival curves in the paper, run the following commands:

```shell
# Convert LEGO-Prover .json logs into aggregated .json files
# with skill reuse information.
# This may take some time.
# This step can be skipped if you directedly downloaded the repo.
# This step is only possible if you download our full raw data, or
# reproduce the experiments.
# It also requires the afp-2019-08-19 AFP be extracted at ./AFP/
# It is available for download at https://sourceforge.net/projects/afp/files/afp-Isabelle2019/
python3 data_analysis/calc_common_ancestors_reuse.py

# Convert LEGO-Prover .json logs into aggregated .json files
# with skill use information.
# This may take some time.
# This step can be skipped if you directedly downloaded the repo.
# This step is only possible if you download our full raw data, or
# reproduce the experiments.
# It also requires the afp-2019-08-19 AFP be extracted at ./AFP/
# It is available for download at https://sourceforge.net/projects/afp/files/afp-Isabelle2019/
python3 data_analysis/calc_common_ancestors_use.py

# Generate the survival function plot for lemmas:
python3 data_analysis/plot_lemma_survival.py

# Generate the survival function plot for tasks:
python3 data_analysis/plot_tasks_vs_threshold.py

# Generate the cost adjusted performance plot
python3 data_analysis/plot_join_cost_exp.py

# Generate the semantic similarity histograms
# Note that a valid OpenAI key is *not* required
# as the embeddings are cached in embeddings_openai3_cache.db
python data_analysis/calc_sim_hist.py
```

Finally, our scripts for performing reuse and use analysis on the original LEGO-Prover logs can be found in the directory [ori_lp_reuse_anlysis](data_analysis/ori_lp_reuse_analysis).
# Other Scripts

Various minor scripts used in our experiments are stored under the [scripts](scripts) directory:

- [1_generate_nonoverlapping_miniF2F_subset.py](scripts/1_generate_nonoverlapping_miniF2F_subset.py)
- [2_calc_expense_ratio.py](scripts/2_calc_expense_ratio.py) generates how many times more expensive LEGO-Prover is per attempt then Draft-Sketch-Prove.

- [generate_paraphrase.py](scripts/generate_paraphrase.py) is used to generate prompt paraphrases used in our prompt stability experiments.
- [generate_miniF2F_subset.py](scripts/generate_miniF2F_subset.py) is used to generate the random 5% subset of the miniF2F test set.
 
- [tabulate_model_accs.py](scripts/tabulate_model_accs.py) generates the table of model accuracies
- [tabulate_model_accs_cost_adj.py](scripts/tabulate_model_accs_cost_adj.py) generates the table of model accuracies, adjusting LP attempts to budget match DSP
- [tabulating_prompt_stab](scripts/tabulating_prompt_stab.py) genrates the table for our prompt stability experiment (i.e., it calculates maximum potential gain and loss).

- [tidyer_exp1.py](scripts/tidyer_exp1.py) Converts LEGO-Prover's standard output into a .csv format. Used to create the LP rows in [exp1.csv](data_analysis/exp1.csv)
- [tidyer_exp2.py](scripts/tidyer_exp2.py) Converts LEGO-Prover's standard output into a .csv format. Used to create the LP rows in [exp2.csv](data_analysis/exp2.csv)
- [tidyer_exp3.py](scripts/tidyer_exp3.py) Converts LEGO-Prover's standard output into a .csv format. Used to create the LP rows in all other experiment .csv files, except for those recording token usage which were manually created.

Note that our [5%](data/full_data/custom/test_rand), [10%](data/full_data/custom/test_rand_10), and [20%](data/full_data/custom/test_rand_20) miniF2F test subsets can be found in [data/full_data/custom](data/full_data/custom). 

# Aditional Experiments

Instructions for reproducing our AgentOptimizer and TroVE experiments can be found at [additional_experiments/agent_optmizer](additional_experiments/agent_optmizer/README.md) and [additional_experiments/trove](additional_experiments/trove/README.md) respectively.

# Data

The raw LEGO-Prover experiment logs are available for download at [https://archive.org/details/readme_20260118](https://archive.org/details/readme_20260118).

# License

This code excluding the [additional_experiments](additional_experiments) directory is modified from the [original LEGO-Prover repository](https://github.com/wiio12/LEGO-Prover.git). The original codebase was released under an MIT license, as is this codebase. The original license can be found [here](https://github.com/wiio12/LEGO-Prover/blob/357672c7751cd0c84aff6bf72a3d1bf97614e81d/LICENSE) is also reproduced at the end of this file. 

The code in [additional_experiments/agent_optmizer](additional_experiments/agent_optmizer) is derived from the [ag2 repository](https://github.com/ag2ai/ag2/blob/main/notebook/agentchat_agentoptimizer.ipynb), which is licensed under the Apache License 2.0 -- see the original license [here](https://github.com/ag2ai/ag2/blob/d69ef9d4ed20c0969a68b7c30a57983857d2af23/LICENSE).

The code in [additional_experiments/trove](additional_experiments/trove) is derived from the [TroVE repository](https://github.com/zorazrw/trove), which is licensed under the CC-BY-SA-4.0 license license -- see [the original license] (https://github.com/zorazrw/trove/blob/c4d16b6a2e38020540db2a611fdea722da6b880c/LICENSE.md).

```
MIT License

Copyright (c) 2023 MineDojo Team

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

Note that the [data/full_data](data/full_data/) directory contains problems from [a variant of the miniF2F dataset](https://github.com/albertqjiang/miniF2F) branched from the [original miniF2F dataset](https://github.com/openai/miniF2F/tree/main). Both are licensed under the [Apache V2.0 license](https://github.com/openai/miniF2F/blob/4e433ff5cadff23f9911a2bb5bbab2d351ce5554/isabelle/LICENSE); thus this directory is licensed under the same license.

# Paper and Citation

If this code was useful to your work then please cite our paper below:

```bibtex
Bibtex coming soon!
```