"""
Script for generating a random size 12 subset of the miniF2F test set.
"""

import random
import os
import shutil

if __name__ == "__main__":
    os.makedirs(os.path.join("data", "full_data", "debug", "test_rand"), exist_ok=True)

    files = []
    for x in os.listdir(os.path.join("data", "full_data", "test")):
        if x.endswith(".json"):
            files.append(x)

    random.seed("Iolanthe")
    files = random.sample(files, 12)

    for file in files:
        shutil.copy(
            os.path.join("data", "full_data", "test", file),
            os.path.join("data", "full_data", "debug", "test_rand", file),
        )
