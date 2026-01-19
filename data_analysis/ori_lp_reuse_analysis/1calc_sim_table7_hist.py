"""
Check embedding similarity of produced proofs and
retrieved lemmas.
Checks embedding similarity *after* removing the statement 
of the proof, which is provided to the LLM, and keep only the body.
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
conn = sqlite3.connect("embeddings_openai3_cache_nov.db")
cursor = conn.cursor()
cursor.execute("""
CREATE TABLE IF NOT EXISTS embeddings (
    hash TEXT PRIMARY KEY,
    text TEXT,
    embedding BLOB
)
""")

# Proofs where extraction of body fails because the LLM
# directly used sledgehammer to solve the proof (i.e., there
# is no proof body)
DIRECT = r"""```isabelle
theory mathd_numbertheory_239
imports Complex_Main 
begin

(* no helper function required in this theorem *)

(* formal statement copy from the input *)
theorem mathd_numbertheory_239 :
  "(\<Sum> k \<in>{1..<13}. k) mod 4 = (2::nat)"
  sledgehammer

end
```"""

DIRECT2 = r"""```isabelle
theory mathd_numbertheory_185
  imports Complex_Main
begin

(* no helper function required in this theorem *)

(* formal statement copy from the input *)
theorem mathd_numbertheory_185:
  fixes n ::nat
  assumes "n mod 5 = 3" 
  shows "(2 * n) mod 5 = 1"
  sledgehammer

end
```"""

DIRECT3 = r"""```isabelle
theory mathd_numbertheory_81
  imports Complex_Main 
begin

(* formal statement copy from the input *)
theorem mathd_numbertheory_81:
  "71 mod 3 = (2::nat)"
  sledgehammer

end
```"""

DIRECT4 = r"""```isabelle
theory mathd_numbertheory_200
imports Complex_Main 
begin

(* no helper function required in this theorem *)

(* formal statement copy from the input *)
theorem mathd_numbertheory_200:
  "139 mod 11 = (7::nat)"
  sledgehammer

end
```"""

DIRECT5 = r"""```isabelle
theory mathd_numbertheory_961
  imports Complex_Main 
begin

(* no helper function required in this theorem *)

(* formal statement copy from the input *)
theorem mathd_numbertheory_961:
  "2003 mod 11 = (1::nat)"
  sledgehammer

end
```"""

DIRECT6 = r"""```isabelle
theory mathd_algebra_304
imports Complex_Main
begin

(* formal statement copy from the input *)
theorem mathd_algebra_304:
  "91^2 = (8281::nat)"
  sledgehammer

end
```"""

DIRECT7 = r"""```isabelle
theory mathd_algebra_176
imports Complex_Main
begin

(* formal statement copy from the input *)
theorem mathd_algebra_176:
  fixes x ::real
  shows "(x + 1)^2 * x = x^3 + 2 * x^2 + x"
  sledgehammer

end
```"""

DIRECT8=r"""```isabelle
theory mathd_numbertheory_169
imports Complex_Main
begin

(* formal statement copy from the input *)
theorem mathd_numbertheory_169:
  "gcd (fact 20) 200000 = (40000::nat)"
  sledgehammer

end
```"""

DIRECT9 = r"""```isabelle
theory mathd_numbertheory_252
imports Complex_Main
begin

(* formal statement copy from the input *)
theorem mathd_numbertheory_252:
  "(fact 7) mod 23 = (3::nat)"
  sledgehammer

end
```"""

OTHER = {r"""```isabelle
theory mathd_numbertheory_101
  imports Complex_Main
begin

(* no helper function required in this theorem *)

(* formal statement copy from the input *)
theorem mathd_numbertheory_101:
  "(17 * 18) mod 4 = (2::nat)"
  (* Step 1: Compute the product of 17 and 18, which is 306. *)
  unfolding power2_eq_square
  sledgehammer

end
```""": r"""  unfolding power2_eq_square
  sledgehammer"""}

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
                elif proof in [DIRECT, DIRECT2, DIRECT3, DIRECT4, DIRECT5, DIRECT6, DIRECT7, DIRECT8, DIRECT9]:
                    proof = "sledgehammer"
                elif proof in OTHER:
                    proof = OTHER[proof]
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

        #if model == '4omini':
        #    print(sorted(kth_sim_in_run[1],reverse=True)[:4])

    # Plot histograms for this run
    plt.figure(figsize=(3.5,2))

    min_val = min(total_kth_sim_in_run[0] + total_kth_sim_in_run[1])
    max_val = max(total_kth_sim_in_run[0] + total_kth_sim_in_run[1])
    for i in [0,1]: #total_kth_sim_in_run:  # : #
        plt.hist(x=total_kth_sim_in_run[i], label='Most Similar Proof' if i == 0 else '2nd Most Similar',  alpha=0.5, density=True, bins=15, range=(min_val,max_val))  # density=True,

    model_name = model.replace('llama3.1', 'Llama3.1').replace('4omini', '4o-mini').replace('qwen3','Qwen3-14B')
    plt.title(f"Distribution of {model_name} Lemmas'\nSemantic Similarities to Proofs", fontsize=9)
    plt.xlabel('Cosine Similarity')
    plt.ylabel('Empirical Density')
    plt.legend(fontsize=8)
    plt.tight_layout()
    
    print(model)
    plt.savefig(f'sem_sim_{model}.png')
    plt.savefig(f'sem_sim_{model}.pdf')
    plt.close()

    return [f'{np.mean(kth_sim_over_runs[i]):.3f} +/- {np.std(kth_sim_over_runs[i],ddof=1):.3f}' for i in sorted(kth_sim_over_runs.keys())]
        


if __name__ == "__main__":
    SPLITS = ['gpt_informal_test.json', 'gpt_informal_valid.json', 'human_informal_test.json', 'human_informal_valid.json']

    table = [['split', '1rst', '2nd', '3rd', '4th', '5th']]
    for model in SPLITS: # 'llama3.1_10_perc', ['exp1_4omini', 'exp4_o3mini', 'exp5_4o']:
        model_path = os.path.join('data_analysis/ori_lp_reuse_analysis/lego_result', f'formatted_{model}')
        row = main(model, model_path)
        if len(row) + 1 >= len(table[0]):
            row = row[:len(table[0]) - 1]
        else:
            row += ['-'] * (len(table[0]) - len(row) - 1)

        table.append([model] + row)

    print(tabulate(table, headers="firstrow"))
