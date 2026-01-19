"""
Utilities for analyzing LEGO-Prover logs
"""

import re


LEMMA_REGEX = re.compile(r"useful skill \d+: ######\s*?```isabelle([\s\S]*?)```")
NAME_REGEX = re.compile(r"(?:lemma|theorem|fun)\s+([^:]+?)\s*:")


def split_lemma_into_statement_and_proof(lemma_str: str):
    lemma = lemma_str.split()
    assert lemma[0] in ["lemma", "theorem", "definition", "fun"], lemma

    statements = []
    proofs = []
    in_statement = None
    for word in lemma:
        if word in ["lemma", "theorem", "definition", "fun"]:
            in_statement = True
            statements.append([])
        elif word in ["proof", "by"]:
            in_statement = False
            proofs.append([])

        assert isinstance(in_statement, bool)
        if in_statement:
            statements[-1].append(word)
        else:
            proofs[-1].append(word)

    return [" ".join(x) for x in statements], [" ".join(x) for x in proofs]


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


def extract_lemmas2(lego_run: dict) -> list:
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


def extract_lemma_names(lemma: str) -> list[str]:
    """
    Extract the name of every lemma & theorem in the provided skill (i.e., lemma)
    """
    return [x.group(1) for x in NAME_REGEX.finditer(lemma)]


def fmt_proof(proof: str, lemma_names: list[str]) -> str:
    """
    Print the proof, highlighting any locations were a string in lemma_names occurs.
    """
    result = proof.split("\n")
    result = [
        f"{x} {'%'*50}" if any(y in x for y in lemma_names) else x for x in result
    ]
    return "\n".join(result)
