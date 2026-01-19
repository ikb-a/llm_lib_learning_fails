"""
Script for generating paraphrased prompts used in 
prompt stability experiments (See Appendix)

Procedure:
1) Generate paraphrases
2) Manual filtering of which calls have equivalent semantics
3) Repeat 1 & 2 until at least 10 paraphrases.
4) Randomly sample 10 of the remaining rephrases. 
"""

import openai
from openai import OpenAI
from azure_key import OPENAI_KEY

# Decomposer
# DSP_PROMPT = """As an mathematician and expert in isabelle theorem prover, your task is to analyze the given theorem (including problem's informal statement, human written informal proof, and formal statement). Provide a better structured step by step proof that closer to isabelle. and request relevant lemmas, theorems that might help in proving this problem.
# You will format your answer as follows:
# - A section with the header `## Structured informal proof` containing the  step-by-step proof.
# - A subsequent section with the header `## Request skills` containing any requested relevant lemmas or theorems
# - Each requested skill is represented by an isabelle code block containing its formal definition"""

# Formalizer
DSP_PROMPT = """As a mathematician familiar with Isabelle, your task is to provide a formal proof in response to a given problem statement.
Your proof should be structured and clearly written, meeting the following criteria:
- It can be verified by Isabelle.
- Each step of the proof should be explained in detail using comments enclosed in "(*" and "*)".
- The explanation for each step should be clear and concise, avoiding any unnecessary or apologetic language.
- You are **strongly encouraged** to create useful and reusable lemmas to solve the problem.
- The lemmas should be as general as possible (generalizable), and be able to cover a large step in proofs (non-trivial).
- You **MUST** copy the input lemma EXACTLY: **without changing whitespace**, without paraphrasing, and without adding comments.
Please ensure that your proof is well-organized and easy to follow, with each step building upon the previous one."""


PARAPHRASE_PROMPT = "Write a paraphrase of the paragraph provided by the user. You **must** preserve the meaning of the paragraph including details, while being super creative with word choice, sentence structure, writing style, tone & sentiment, etc..."

MODEL_INPUT = f'{PARAPHRASE_PROMPT}\n\n"{PARAPHRASE_PROMPT}"'

if __name__ == "__main__":
    client = OpenAI(api_key=OPENAI_KEY)

    messages = [
        {"role": "system", "content": PARAPHRASE_PROMPT},
        {"role": "user", "content": DSP_PROMPT},
    ]

    response = client.chat.completions.create(
        messages=messages,
        temperature=1,
        model="gpt-3.5-turbo-0125",
        max_tokens=4096,
        stop="Informal",
    )

    print(response.choices[0].message.content)
