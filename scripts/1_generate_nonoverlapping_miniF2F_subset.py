"""
Python script for creating a random subset of the miniF2F test
set, which does not overlap with any of the questions 
contained within the directories listed in EXCLUDE_DIRS.
"""

import os
import shutil
import random

# Directory containing all questions to sample from
SOURCE_DIR = "data/full_data/test"

# Directories that for which we do not want an overlap of questions
EXCLUDE_DIRS = [
    "data/full_data/custom/test_rand",
    "data/full_data/custom/test",
    "data/full_data/custom/test_rand_10",
]

OUT_DIR = "data/full_data/custom/test_rand_20"  #'test_rand_10'
SAMPLE_SIZE = 49  # 12 * 2

if __name__ == "__main__":
    test_files = list(os.listdir(SOURCE_DIR))
    exclude = []
    for exclude_dir in EXCLUDE_DIRS:
        exclude.extend(os.listdir(exclude_dir))

    population = [x for x in test_files if x.endswith(".json") and x not in exclude]
    sample = random.sample(population, SAMPLE_SIZE)

    os.makedirs(OUT_DIR, exist_ok=False)

    for filename in sample:
        shutil.copy(os.path.join(SOURCE_DIR, filename), os.path.join(OUT_DIR, filename))
