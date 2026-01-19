"""
Helper script for converting LEGO-Prover standard output logs into
a single .csv file.

Unlike other experiments, results can be split over several *.out files :(
So need directory to summarize

This script is for Experiment 1 (i.e., gpt-4o-mini evaluated on the entire
test dataset).
"""

import argparse
import os


def split(input_path: str):
    idx = len(input_path) - input_path[::-1].index("/") - 1
    return input_path[:idx], input_path[idx + 1 :]


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("dataset", choices=["test"])
    parser.add_argument(
        "dirpath",
        type=str,
        help="Path to a directory of .out files containing LEGO-Provers's standard output",
    )
    parser.add_argument("run", type=int)
    args = parser.parse_args()

    assert args.dirpath.endswith("/")

    filenames = list(x for x in os.listdir(args.dirpath) if x.endswith(".out"))
    filenames.sort()

    all_solved_problems = []
    for filename in filenames:
        with open(os.path.join(args.dirpath, filename), "r") as infile:
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

                print(f"lp,{args.dataset},{args.run},{attempt},{problem}")
