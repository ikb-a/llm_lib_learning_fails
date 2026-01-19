"""
Helper script for converting LEGO-Prover standard output logs into
a single .csv file.

Unlike other experiments, results can be split over several *.out files :(
So need directory to summarize

This script is for Experiments 3 onwards (i.e., experiments with LLMs
other than gpt-4o-mini being performed on the 5%, 10%, or 20% random subsets
of the test set).
"""

import argparse
import os


def split(input_path: str):
    idx = len(input_path) - input_path[::-1].index("/") - 1
    return input_path[:idx], input_path[idx + 1 :]


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "dataset",
        choices=["test12", "val12", "test24", "test49"],
        help="test12 corresponds to 5%, test24 corresponds to 10%, test49 is 20%.",
    )

    parser.add_argument(
        "filepath",
        type=str,
        help="Path to a directory of .out files containing LEGO-Provers's standard output",
    )
    args = parser.parse_args()

    assert args.filepath.endswith("_")
    target_dir, target_filename = split(args.filepath)

    filenames = list(x for x in os.listdir(target_dir) if x.startswith(target_filename))
    filenames.sort()

    add_one = False  # Shift if accidentally 0-indexed

    for filename in filenames:
        all_solved_problems = []
        run = int(filename[len(target_filename) : len(target_filename) + 1])
        if run == 0:
            add_one = True
        run += add_one

        with open(os.path.join(target_dir, filename), "r") as infile:
            data = infile.readlines()

        for line in data:
            if "True" in line:
                problem = line[: line.index(".json")]
                _, problem = split(problem)

                # Skip line if LP already solved in a previous attempt
                if problem in all_solved_problems:
                    continue
                all_solved_problems.append(problem)

                attempt = line[line.index("try: ") + len("try: ") :]
                attempt = int(attempt[: attempt.index(",")])

                print(f"lp,{args.dataset},{run},{attempt},{problem}")
