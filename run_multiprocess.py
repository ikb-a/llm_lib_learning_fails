"""
Main script for running the LEGO-Prover.
"""

import argparse
import logging
import multiprocessing as mp
import os
import pytz
from datetime import datetime
import json
from datetime import datetime, timedelta

from lego_prover.env.chromas import ChromaBridge
from lego_prover.evolver import Evolver
from lego_prover.prover import Prover
import lego_prover.utils as U

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="LEGO-Prover")
    parser.add_argument(
        "--resume", action="store_true", help="whether to resume from the checkpoint"
    )
    parser.add_argument(
        "--data_split",
        type=str,
        default="valid",
        help="data split to use in the miniF2F dataset",
    )
    parser.add_argument(
        "--ckpt_dir",
        type=str,
        default="checkpoints/lego_prover_reprod1",
        help="path to the checkpoint directory",
    )
    parser.add_argument(
        "--isabelle_path",
        type=str,
        default="~/PFS/Isabelle2022",
        help="path to the Isabelle2022 directory",
    )
    parser.add_argument(
        "--model_name",
        type=str,
        choices=["gpt-4o-mini", "gpt-4o", "o3-mini", "Meta-Llama-3.1-8B-Instruct", "Qwen3-14B"],
        default="gpt-4o-mini",  # NOTE: Azure does not allow gpt-4o-mini-2024-07-18
        help="OpenAI model name",
    )
    parser.add_argument(
        "--base_url",
        type=str,
        default=None,
        help="base_url for a local vLLM server providing an OpenAI interface",
    )
    parser.add_argument(
        "--temperature",
        type=float,
        default=0.7,
        help="temperature for sampling the LLM",
    )
    parser.add_argument(
        "--num_prover", type=int, default=3, help="number of prover processes"
    )
    parser.add_argument(
        "--num_evolver", type=int, default=8, help="number of evolver processes"
    )
    parser.add_argument(
        "--num_attempts",
        type=int,
        default=100,
        help="number of proving attempts for each problem in the dataset",
    )

    # Added arguments
    parser.add_argument(
        "--isolate_v1",
        action="store_true",
        help="Whether to prevent cross-task sharing of information.",
    )
    parser.add_argument(
        "--isolate_v2",
        action="store_true",
        help="Whether to prevent cross-task sharing of information. V2 fixes evolver to only retrieve skill manager's task.",
    )

    parser.add_argument(
        "--augment_retrieved",
        type=str,
        default=None,
        help="If provided with a .json containing a list of paths to .thy files, limit retrieval from library and pad the rest with random subsets of these theorems",
    )

    parser.add_argument(
        "--max_duration",
        type=float,
        default=24 * 30,
        help="Maximum job duration. Letting the system shut itself down is more likely to make resumption successful. Defaults to 30 days. Will run a bit over this limit. Safest to assume will go over by an hour or so.",
    )
    parser.add_argument(
        "--max_calls_per_s",
        type=float,
        default=1 / (60 * 5),  # Default to 1 call per 5 minutes
        help="Maximum calls per second, across all processes. Set to a negative value to disable rate limiting.",
    )

    parser.add_argument(
        "--decomposer_prompt",
        type=str,
        default=None,
        help="name of .txt file (excluding file extension) container the decomposer prompt to use in the prover.",
    )
    parser.add_argument(
        "--formalizer_prompt",
        type=str,
        default=None,
        help="name of .txt file (excluding file extension) container the formalizer prompt to use in the prover.",
    )
    parser.add_argument(
        "--port_offset",
        type=int,
        default=0,
        help="add this much to the port numbers allocated",
    )
    parser.add_argument(
        "--evolve_prompts",
        type=str,
        default="lego_prover/prompts/skill_evolver",
        help="path to directory containing a different set of evolver prompts",
    )
    # model_tokenizer_name
    parser.add_argument(
        "--model_tokenizer_name",
        type=str,
        default=None,
        help="name for the model on huggingface for finding the tokenizer; not required for OpenAI models",
    )

    args = parser.parse_args()

    # Exit if base_url is malformed
    if args.base_url is not None and not args.base_url.startswith('http'):
        print(f"Bad base_url: {args.base_url}")
        exit(-1)

    # Adjust rate limit to distribute between each process
    args.max_calls_per_s = args.max_calls_per_s / (args.num_prover + args.num_evolver)
    # Disable rate limiting if a negative value passed in
    if args.max_calls_per_s < 0:
        print("Rate limiting disabled")
        args.max_calls_per_s = None

    if args.model_name == "o3-mini":
        print("-" * 40)
        print("NOTE: o3-mini will ignore temperature settings.")
        print("NOTE: o3-mini, therefore max tokens also forcibly set to 8192.")
        print("-" * 40)

    if args.decomposer_prompt is not None:
        print(f"Decomposer prompt switched to {args.decomposer_prompt}")
    if args.formalizer_prompt is not None:
        print(f"Formalizer prompt switched to {args.formalizer_prompt}")

    if args.evolve_prompts != "lego_prover/prompts/skill_evolver":
        print(f"Evolver prompts switched to {args.evolve_prompts}")

    # Make sure we have the right Isabelle present (i.e., 120s timeout)
    JAR_PATH = "lego_prover/env/Portal-to-ISAbelle/PISA-assembly-0.1.jar"
    if os.path.exists(JAR_PATH):
        print(f"Exiting -- .jar path exists, unsure of Isabelle timeout. {JAR_PATH}")
        exit(-1)
    else:
        # NOTE: Isabelle should be compiled (making sure that the timeout is set correctly, see
        # https://github.com/albertqjiang/draft_sketch_prove/issues/3 ), and then the result renamed
        # from 'PISA-assembly-0.1.jar' to 'PISA-assembly-120s-0.1.jar'
        print("Setting up, copying .jar")
        os.symlink(
            os.path.realpath(
                "lego_prover/env/Portal-to-ISAbelle/target/scala-2.13/PISA-assembly-120s-0.1.jar"
            ),
            JAR_PATH,
        )

    start_time = datetime.now()
    end_time = start_time + timedelta(hours=args.max_duration)

    if args.augment_retrieved is not None:
        with open(args.augment_retrieved, "r") as infile:
            args.augment_retrieved = json.load(infile)

    resume = args.resume
    data_split = args.data_split
    ckpt_dir = args.ckpt_dir
    isabelle_path = args.isabelle_path
    model_name = args.model_name
    temperature = args.temperature
    number_of_prover_processes = args.num_prover
    number_of_evolver_processes = args.num_evolver
    number_of_prover_attempts = args.num_attempts
    isolate_v1 = args.isolate_v1
    isolate_v2 = args.isolate_v2

    if os.path.exists(ckpt_dir) and not resume:
        print(
            f"the checkpoint directory {ckpt_dir} already exists, and"
            + f"you are not resuming from it; exiting."
        )
        os.remove(JAR_PATH)
        exit(-1)

    # load miniF2F tasks and resume from the checkpoint
    miniF2F_tasks = mp.Queue()
    problem_names = []

    completed_tasks = []
    failed_tasks = []

    if resume:
        if os.path.exists(f"{ckpt_dir}/curriculum/completed_tasks.json"):
            completed_tasks = U.load_json_list(
                f"{ckpt_dir}/curriculum/completed_tasks.json"
            )
        if os.path.exists(f"{ckpt_dir}/curriculum/failed_tasks.json"):
            failed_tasks = U.load_json_list(f"{ckpt_dir}/curriculum/failed_tasks.json")
        print("Current progress: ", len(completed_tasks) + len(set(failed_tasks)))
    
        
    for name in os.listdir(f"data/full_data/{data_split}"):
        path = os.path.join(f"data/full_data/{data_split}", name)
        context = U.load_json(path)
        problem_names.append((path, len(context["informal_proof"])))
    problem_names = sorted(problem_names, key=lambda x: x[1])
    problem_names = [pn[0] for pn in problem_names]
    problem_names = problem_names * number_of_prover_attempts  # 10 * 20 = 200 sketch
    for pn in problem_names:
        if pn in completed_tasks:
            continue
        if pn in failed_tasks:
            failed_tasks.remove(pn)
            continue
        miniF2F_tasks.put(pn)
    print(f"Sketch to finish: {miniF2F_tasks.qsize()}")

    # setup multiprocessing logger
    start_time = datetime.now(pytz.timezone("Asia/Shanghai")).strftime("%Y%m%d_%H%M%S")

    os.makedirs(f"logs/prover/{start_time}_logs", exist_ok=True)
    for rank in range(number_of_prover_processes):
        logger = logging.getLogger(f"prover-{rank}")
        handler = logging.FileHandler(f"logs/prover/{start_time}_logs/rank_{rank}.log")
        formatter = logging.Formatter(
            "%(asctime)s - %(name)s - %(levelname)s - %(message)s"
        )
        handler.setFormatter(formatter)
        logger.addHandler(handler)
        logger.setLevel(logging.INFO)

    os.makedirs(f"logs/evolver/{start_time}_logs", exist_ok=True)
    for evolver_rank in range(number_of_evolver_processes):
        evolver_rank += number_of_prover_processes
        logger = logging.getLogger(f"evolver-{evolver_rank}")
        handler = logging.FileHandler(
            f"logs/evolver/{start_time}_logs/rank_{evolver_rank}.log"
        )
        formatter = logging.Formatter(
            "%(asctime)s - %(name)s - %(levelname)s - %(message)s"
        )
        handler.setFormatter(formatter)
        logger.addHandler(handler)
        logger.setLevel(logging.INFO)

    # define the function to run the prover and evolver
    def run_prover(
        rank, tasks, skill_manager_lock, curriculum_agent_lock, chroma_bridge
    ):
        server_port = 8051 + rank + args.port_offset

        prover = Prover(
            rank=rank,
            isabelle_path=isabelle_path,
            server_port=server_port,
            model_name=model_name,
            base_url=args.base_url,
            skill_manager_lock=skill_manager_lock,
            action_agent_task_max_retries=1,
            curriculum_task_type="queue_curriculum",
            curriculum_agent_lock=curriculum_agent_lock,
            resume=resume,
            temperature=temperature,
            miniF2F_tasks=tasks,
            ckpt_dir=ckpt_dir,
            chroma_bridge=chroma_bridge,
            isolate=isolate_v1 or isolate_v2,
            alternative_theorems_list=args.augment_retrieved,
            end_time=end_time,
            max_calls_per_s=args.max_calls_per_s,
            decomposer_filename=args.decomposer_prompt,
            formalizer_filename=args.formalizer_prompt,
            model_tokenizer_name=args.model_tokenizer_name,
        )
        prover.learn()
        print(f"Prover-{rank} done!", flush=True)

        # Try to do some cleanup before exit
        prover.env.close()
        logging.shutdown()

        # Hard exit
        os._exit(0)

    def run_evolver(rank, skill_manager_lock, chroma_bridge, job_queue):
        server_port = 8011 + rank + args.port_offset
        evolver = Evolver(
            rank=rank,
            isabelle_path=isabelle_path,
            ckpt_dir=ckpt_dir,
            server_port=server_port,
            data_split=data_split,
            skill_manager_lock=skill_manager_lock,
            model_name=model_name,
            base_url=args.base_url,
            temperature=temperature,
            chroma_bridge=chroma_bridge,
            miniF2F_tasks=job_queue,
            isolate=isolate_v1 or isolate_v2,
            isolate_v2=isolate_v2,
            alternative_theorems_list=args.augment_retrieved,
            data_directory=f"data/full_data/{data_split}",
            end_time=end_time,
            max_calls_per_s=args.max_calls_per_s,
            evolve_prompt_dir=args.evolve_prompts,
            model_tokenizer_name=args.model_tokenizer_name,
        )
        evolver.evolve()
        print(f"Evolver-{rank} done!", flush=True)

        # Try to do some cleanup before exit
        evolver.env.close()
        logging.shutdown()

        # Hard exit
        os._exit(0)

    processes = []
    skill_manager_lock = mp.Lock()
    curriculum_agent_lock = mp.Lock()

    if not (isolate_v1 or isolate_v2):
        chroma_bridge = ChromaBridge(ckpt_path=ckpt_dir, resume=resume)
    else:
        # If isolated, create a distinct ChromaBridge for each problem
        # Note the subdirectories for the checkpoint paths
        chroma_bridge = {
            U.problem_id(x): ChromaBridge(
                ckpt_path=os.path.join(ckpt_dir, U.problem_id(x)),
                resume=resume,
                name=f"chroma_worker_{U.problem_id(x)}",
            )
            for x in set(problem_names)
        }

    # creating processes
    for rank in range(number_of_prover_processes):
        p = mp.Process(
            target=run_prover,
            args=(
                rank,
                miniF2F_tasks,
                skill_manager_lock,
                curriculum_agent_lock,
                chroma_bridge,
            ),
            name=f"Prover{rank}",
        )
        processes.append(p)
        p.start()

    for rank in range(number_of_evolver_processes):
        rank += number_of_prover_processes
        p = mp.Process(
            target=run_evolver,
            args=(rank, skill_manager_lock, chroma_bridge, miniF2F_tasks),
            name=f"Evolver{rank}",
        )
        processes.append(p)
        p.start()

    # completing process
    for p in processes:
        print(f"Waiting on process {p}", flush=True)
        p.join()

    if datetime.now() > end_time:
        print("WARNING: Likely exiting early as max job duration exceeded.")

    print("All processes done", flush=True)

    # Remove the Isabelle .jar
    os.remove(JAR_PATH)

    if miniF2F_tasks.qsize() == 0:
        print("Queue is empty, marking done file")
        with open('JOB_DONE.txt', 'w') as outfile:
            print("JOB DONE!", file=outfile)

    # Hard exit
    logging.shutdown()
    os._exit(0)
