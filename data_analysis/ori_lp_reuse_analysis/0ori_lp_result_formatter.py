"""Convert original LP results to the correct format.
This step can be skipped as the converted files are already in this repo.
"""
import json 
from pathlib import Path
import re 

LEMMA_REGEX = re.compile(r"useful skill \d+: ######\s*?```isabelle([\s\S]*?)```")


def extract_lemmas(lego_run: dict) -> list:
    """
    Extract the skills (i.e., lemmas) that were provided as part of the prompt to the prover (i.e., LLM)
    """
    prover_input = lego_run["prover_conversation"]["human"]

    # Remove the problems
    prover_input = prover_input[: prover_input.index("## Problems")]

    assert "useful skill" in prover_input, prover_input
    results = []
    for lemma in LEMMA_REGEX.finditer(prover_input):
        results.append(lemma.group(1).strip())

    return results


ROOT = Path('data_analysis/ori_lp_reuse_analysis/lego_result/')
filenames = ['gpt_informal_test.json', 'gpt_informal_valid.json', 'human_informal_test.json', 'human_informal_valid.json']

for file in filenames:
    reformatted = {'1': {'lemma_to_task': {}, 
                         'task_to_proof': {},
                         'task_to_lemma': {}}}

    with open(ROOT/file, 'r') as infile:
        data = json.load(infile)

    for success in data:
        task_name = success["task"]
        lemmas = extract_lemmas(success)
        proof = success['prover_conversation']['ai']

        for lemma in lemmas:
            if lemma not in reformatted['1']['lemma_to_task']:
                reformatted['1']['lemma_to_task'][lemma] = []
            reformatted['1']['lemma_to_task'][lemma].append(task_name)

        assert task_name not in reformatted['1']['task_to_lemma'], reformatted['1']
        reformatted['1']['task_to_lemma'][task_name] = lemmas 
        assert task_name not in reformatted['1']['task_to_proof']
        reformatted['1']['task_to_proof'][task_name] = proof 

    with open(ROOT/f'formatted_{file}', 'w') as outfile:
        json.dump(reformatted, outfile, indent=2, sort_keys=True) 
    


