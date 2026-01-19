# AgentOptimizer Experiments

## Environment Setup

These experiments were performed with Python3.10

To set up the environment, please run:

```
python3.10 -m venv env
source env
pip install -r requirements.txt
```

Next, set your OpenAI API key in [openai_key.py](openai_key.py), and Azure credentials in [azure_key.py](azure_key.py). By default Azure credentials will be used, but OpenAI credentials can be used instead by setting the `--open_ai` flag.

## Experiments

### Direct ReAct Baseline Evaluation

```bash
source env/bin/activate
python direct_prompt.py --dataset "${dataset}" --run_id "gpt4o_0" --model 'gpt-4o'
```

To run on 4o-mini, replace the argument to `--model` with `gpt-4o-mini`

The choices of dataset are: 'algebra', 'counting_and_probability', 'geometry', 'intermediate_algebra', 'number_theory', 'prealgebra', and 'precalculus'

### AgentOptimizer Evaluation

To run AgentOptimizer with 10 epochs of training:

```bash
source env/bin/activate
python train.py --open_ai --dataset "${dataset}" --run_id "gpt4o_0_10epochs" --model 'gpt-4o' --epochs 10
```

### Data Analysis

We release our experiment logs and analysis scripts. Logs from our non-training runs can be found in [outputs_direct](outputs_direct). Logs from our experiments under AgentOptimizer can be found in [outputs_train](outputs_train).

To generate our table of direct reuse, please run `python3 0000_calc_dir_reuse.py`

To generate our tables of MATH performance, please run `python3 0000_tabulate_col.py`

## License

This directory is derived from: https://github.com/ag2ai/ag2/blob/main/notebook/agentchat_agentoptimizer.ipynb and released under [the same license](https://github.com/ag2ai/ag2/blob/d69ef9d4ed20c0969a68b7c30a57983857d2af23/LICENSE)
