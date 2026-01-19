# TroVE Experiment

To run our K=15 SKIP experiment on TroVE, clone [the TroVE repository](https://github.com/zorazrw/trove), set up the environment as per their instructions, replace [baseline.py](baseline.py) in the root directory, and run:

```bash
python baseline.py --seed 34 --task-name "tabmwp" --suffix "primitive" --model_name "codellama/CodeLlama7b-Instruct-hf" --num_return_sequences 15
```
# License

The contents of this directory are shared under the CC-BY-SA-4.0 license, and are derived from work under the same license -- see https://github.com/zorazrw/trove/blob/c4d16b6a2e38020540db2a611fdea722da6b880c/LICENSE.md