"""
Try to tabulate, for each retrieved lemma, average similarity to most similar proof, second most similar proof, etc...

This just extracts useful dictionaries saved in ./similarity which, for each run, map lemma_to_task, task_to_lemma, task_to_proof

This code has already been run, with the results saved to the "similarity" directory.
Re-running this script requires the raw LP logs.
"""

import re
import os
import json
#from direct_reuse_analysis import print_frequency
from tqdm import tqdm
from collections import defaultdict
import matplotlib.pyplot as plt
import numpy as np
import copy
import random
import hashlib
import sqlite3
import openai
from azure_key import OPENAI_KEY
from langchain_openai import OpenAIEmbeddings
import numpy as np
underlying_embeddings = OpenAIEmbeddings(api_key=OPENAI_KEY, model="text-embedding-ada-002")

# Connect to SQLite
conn = sqlite3.connect("embeddings_cache.db")
cursor = conn.cursor()
cursor.execute("""
CREATE TABLE IF NOT EXISTS embeddings (
    hash TEXT PRIMARY KEY,
    text TEXT,
    embedding BLOB
)
""")


def serialize_embedding(embedding):
    return embedding.tobytes()

def deserialize_embedding(blob):
    return np.frombuffer(blob, dtype=np.float32)


def get_embedding(text):
    """Convert text to np array of embedding. Cache results to sqlite db"""
    # Hash the text
    text_hash = hashlib.sha256(text.encode()).hexdigest()

    # Check cache
    cursor.execute("SELECT embedding FROM embeddings WHERE hash = ?", (text_hash,))
    result = cursor.fetchone()
    if result:
        return deserialize_embedding(result[0])  # Cached embedding

    # Get from OpenAI
    print("GO TO OPENAI: CACHE FAILURE")
    #response = openai.embeddings.create(input=[text], model="text-embedding-3-small")
    #embedding = response['data'][0]['embedding']

    embedding = np.array(underlying_embeddings.embed_query(text), dtype=np.float32)

    # Store in cache
    cursor.execute("INSERT INTO embeddings (hash, text, embedding) VALUES (?, ?, ?)",
                   (text_hash, text, serialize_embedding(embedding)))
    conn.commit()

    return embedding


random.seed(42)

COMMENT_REGEX = re.compile(r"\(\*[\s\S]*?\*\)")

LEMMA_REGEX = re.compile(r"useful skill \d+: ######\s*?```isabelle([\s\S]*?)```")
def extract_lemmas(lego_run: dict) -> list:
    """
    Extract the skills (i.e., lemmas) that were provided as part of the prompt to the prover (i.e., LLM).
    Unlike extract_lemmas, this version uses the different keys that LP's repo generates.
    """
    prover_input = lego_run["action_agent_conversation"]["action_agent_human0"]

    # Remove the problems
    prover_input = prover_input[: prover_input.index("## Problems")]

    assert "useful skill" in prover_input, prover_input
    results = []
    for lemma in LEMMA_REGEX.finditer(prover_input):
        results.append(lemma.group(1).strip())

    return results



def load_successes(results_path):
    """
    Iterate through LEGO-Prover json logs folder and load all
    succesful attempts.
    """
    # ======================================================
    # Loading data.
    # Iterate through dir, check which suceeded, store filtered json dicts in a list.
    lego_results = []

    for attempt in tqdm(os.listdir(results_path), disable=True):
        if not attempt.endswith(".json"):
            continue

        with open(os.path.join(results_path, attempt), "r") as infile:
            attempt_data = json.load(infile)

        if not attempt_data["success"]:
            continue
        lego_results.append(attempt_data)

    return lego_results


def find_parents(lego_results) -> tuple[dict[str, set], dict[str, set]]:
    """
    Find lemmas directly retrieved and used in generating solution.
    """
    parents = {}  # Map solved task to a set of its parents (i.e., lemmas used for solving)
    children = defaultdict(
        lambda: set()
    )  # Map lemmas to a set of its children solved tasks

    for succesful_run in lego_results:
        assert succesful_run["success"]
        task = succesful_run["task"]
        lemmas = set(extract_lemmas(succesful_run))
        parents[task] = lemmas

        for lemma in lemmas:
            children[lemma].add(task)

    return children, parents


def process_run(datapath, run_idx, output_path):
    print("=" * 100)
    print(datapath)
    assert f"run{run_idx}" in str(datapath) or f"_{run_idx}/" in str(datapath) or f'_idx{run_idx-1}' in str(datapath)

    # Load data
    successes = load_successes(datapath)

    print(f"{len(successes)} Solved problems")

    # Create dictionary to solutions
    answers = {}
    for succ in successes:
        assert succ["success"]
        answers[succ["task"]] = re.sub(COMMENT_REGEX, "", succ["conversations"][0][-1])

    # For each solved problem, find its child lemmas
    # & count the occurences of each child lemma
    # NOTE: children maps lemmas to tasks in which they were used
    # NOTE: parents maps tasks to lemmas used in completion
    children, parents = find_parents(successes)

    # Convert from str->set to str->list for easier serialization
    children = {lemma: list(children[lemma]) for lemma in children}
    parents = {task: list(parents[task]) for task in parents}

    return {'lemma_to_task': children, 'task_to_lemma': parents, 'task_to_proof': answers}


def main(data_paths, output_path, amortized_data_name: str):
    os.makedirs(output_path,exist_ok=True)
    # 1) Need mapping from proof to child lemmas
    amort_path = os.path.join(output_path, amortized_data_name + ".json")
    if os.path.exists(amort_path):
        with open(amort_path, "r") as infile:
            amortized_data = json.load(infile)
    else:
        amortized_data = {}  

    if len(amortized_data) == 0:
        for i, datapath in enumerate(data_paths):
            amortized_data[i+1] = process_run(datapath, i + 1, output_path)

    else:
        print(f"Amortized file {amort_path} already exists? Exiting.")
        return 

    with open(amort_path, "w") as outfile:
        json.dump(amortized_data, outfile, indent=2, sort_keys=True)



if __name__ == "__main__":
    for input_path, output_path in [
        # o3-mini, experiment 4
        (
            [
                f"ablation_experiment_results/22_exp4_test_split_o3mini/run{i}/checkpoints/22_exp4_test_split_o3mini_{i}/json_logs/"
                for i in range(1, 4)
            ],
            "data_analysis/similarity/exp4_o3mini",

        ),
        # 4o, experiment 5
        (
            [
                f"ablation_experiment_results/21_exp5_test_split_4o_prompt2/checkpoints/21_exp5_test_split_4o_prompt2_{i}/json_logs/"
                for i in range(1, 4)
            ],
            "data_analysis/similarity/exp5_4o",

        ),
        # Exp 1, 4o-mini
        (
            [
                f"ablation_experiment_results/20_exp1_test/run{i}/checkpoints/20_exp1_test_{i}/json_logs/"
                for i in range(1, 4)
            ],
            "data_analysis/similarity/exp1_4omini",

        ),

        # Llama 3.1, 10%
        (
            [
                f"ablation_experiment_results_arr_sept/10_perc_test/lp/re1_exp4_Meta-Llama-3.1-8B-Instruct_idx{i-1}/json_logs/"
                for i in range(1, 4)
            ],
            "data_analysis/similarity/llama3.1_10_perc",
        ),

        # Llama 3.1, 100%
        (
            [
                f"ablation_experiment_results_arr_sept/full_test/lp/full_re1_exp4_Meta-Llama-3.1-8B-Instruct_idx{i-1}/json_logs/"
                for i in range(1, 4)
            ],
            "data_analysis/similarity/full_llama3.1",
        ),

        # Qwen3, 10%
        (
            [
                f"ablation_experiment_results_arr_sept/10_perc_test/lp_qwen/re1_exp4_qwen3_14B_Qwen3-14B_idx{i-1}/json_logs/"
                for i in range(1, 4)
            ],
            "data_analysis/similarity/10perc_qwen3",
        ),
    ]:
        main(
            data_paths=input_path,
            output_path=output_path,
            amortized_data_name="ada_sim",
        )
