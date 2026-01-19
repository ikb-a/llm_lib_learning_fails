"""
Produces a histogram of lemma semantic similarities to
proof.
The statement of the proof (provided to the LLM) is removed,
keeping only the body for semantic similarity.

This script requires data extracted from the raw logs; this
data should already be in this repository. To re-extract these
values from the raw data, run data_analysis/calc_sim_table_generated_amortized_sims.py
"""
import os
import json
#from direct_reuse_analysis import print_frequency
from collections import defaultdict
#import matplotlib.pyplot as plt
import numpy as np
import random
import hashlib
import sqlite3
import openai
from azure_key import OPENAI_KEY
from langchain_openai import OpenAIEmbeddings
import numpy as np
underlying_embeddings = OpenAIEmbeddings(api_key=OPENAI_KEY, model="text-embedding-3-large")
from numpy.linalg import norm
from tabulate import tabulate
import matplotlib.pyplot as plt
plt.rcParams["font.family"] = "serif"

def cos_sim(A,B) -> float:
    return float(np.dot(A, B) / (norm(A) * norm(B)))

# Connect to SQLite
conn = sqlite3.connect("embeddings_openai3_cache.db")
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


def main(model, model_path):
    with open(model_path, 'r') as infile:
        data = json.load(infile)

    kth_sim_over_runs = defaultdict(lambda: list())  # Used to compute average over run averages
    kth_count_over_runs = defaultdict(lambda: list())

    total_kth_sim_in_run = defaultdict(lambda:list())

    for run_name, run in data.items():
        kth_sim_in_run = defaultdict(lambda: list()) # used to compute run average

        # Lemma to sim of nth most similar proof
        for lemma, tasks in run['lemma_to_task'].items():

            lemma_embed = get_embedding(lemma)

            proofs = {}
            for task in tasks:
                proof = run['task_to_proof'][task]

                if 'proof -' in proof:
                    proof = proof[proof.index('proof -') + len('proof -'):]
                elif 'by' in proof:
                    proof = proof[proof.index('by') + len('by'):]
                else:
                    print(proof)
                    exit(-1)

                proofs[task] = proof

            proof_sims = [cos_sim(lemma_embed, get_embedding(proofs[task])) for task in tasks]
            proof_sims.sort(reverse=True)

            for i, sim in enumerate(proof_sims):
                kth_sim_in_run[i].append(sim)

        for i in kth_sim_in_run:
            #kth_sim_over_runs[i].append(sum(kth_sim_in_run[i])/len(kth_sim_in_run[i]))
            kth_sim_over_runs[i].append(max(kth_sim_in_run[i]))

            kth_count_over_runs[i].append(len(kth_sim_in_run[i]))

            total_kth_sim_in_run[i] += kth_sim_in_run[i]

        if model == '4omini':
            print(sorted(kth_sim_in_run[1],reverse=True)[:4])

    # Plot histograms for this run
    plt.figure(figsize=(3.5,2))

    min_val = min(total_kth_sim_in_run[0] + total_kth_sim_in_run[1])
    max_val = max(total_kth_sim_in_run[0] + total_kth_sim_in_run[1])
    for i in [0,1]: #total_kth_sim_in_run:  # : #
        plt.hist(x=total_kth_sim_in_run[i], label='Most Similar Proof' if i == 0 else '2nd Most Similar',  alpha=0.5, density=True, bins=15, range=(min_val,max_val))  # density=True,

    model_name = model.replace('llama3.1', 'Llama3.1').replace('4omini', '4o-mini').replace('qwen3','Qwen3-14B')
    plt.title(f"Distribution of {model_name} Lemmas'\nSemantic Similarities to Proofs")
    plt.xlabel('Cosine Similarity')
    plt.ylabel('Empirical Density')
    plt.legend(fontsize=8)
    plt.tight_layout()
    
    plt.savefig(f'sem_sim_{model}.png')
    plt.close()

    return [f'{np.mean(kth_sim_over_runs[i]):.3f} +/- {np.std(kth_sim_over_runs[i],ddof=1):.3f}' for i in sorted(kth_sim_over_runs.keys())]
        


if __name__ == "__main__":
    table = [['model', '1rst', '2nd', '3rd', '4th', '5th']]
    for model in ['exp4_o3mini', 'exp5_4o', 'exp1_4omini',  'full_llama3.1', '10perc_qwen3']: # 'llama3.1_10_perc', ['exp1_4omini', 'exp4_o3mini', 'exp5_4o']:
        model_path = os.path.join('data_analysis/similarity', model, 'ada_sim.json')
        row = main(model.split('_')[-1], model_path)
        if len(row) + 1 >= len(table[0]):
            row = row[:len(table[0]) - 1]
        else:
            row += ['-'] * (len(table[0]) - len(row) - 1)

        table.append([model.split('_')[-1]] + row)

    print(tabulate(table, headers="firstrow"))
