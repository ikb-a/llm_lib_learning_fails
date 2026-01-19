"""
Generalize:
Relax Constraints: Identify which assumptions or constraints can be relaxed without making the theorem false.
Broaden Definitions: If a concept is defined very narrowly, see if a more general definition would also work.
Identify Parameters: If numbers are used, identify them as parameters and explore how they might change.
Extend Dimensions: If the problem is defined in a specific number of dimensions, consider if it holds in more or fewer dimensions.

Identify Key Concepts: Determine the essential ideas, methods, or theorems that are crucial to solving the initial problem.
Parameterize: If the problem involves specific numbers, generalize it by replacing these with variables.
Isolate Techniques: Note any specific techniques used to solve the problem—these can often be applied elsewhere.

Alter Conditions: Introduce small changes to the original problem (e.g., add constraints or relax some conditions) and attempt to solve it again.
Scale Complexity: Try both simpler and more complicated versions of the problem to see how the approach adapts.
Switch Domains: Apply the core principles or techniques to problems in other areas of mathematics or even other disciplines.

Identify Similarities: Look for problems that seem unrelated but share the same core principle or solution technique.
Draw Analogs: Sometimes, the structure of a problem in one area of mathematics mirrors the structure in another area. Recognizing these analogs can help you transfer knowledge.
"""

import os
import re
import random
import traceback
from datetime import datetime, timedelta
from lego_prover.agents.skill import SkillManager, Provenance
from lego_prover.env.chromas import ChromaBridge
from lego_prover.env.isa_bridge import IsabelleEnv
import lego_prover.utils as U
from langchain.prompts import SystemMessagePromptTemplate
from typing import Optional

from lego_prover.utils.langchain_utils import LLMMixture

import multiprocessing as mp

import logging
from time import sleep

EVOLVE_TYPES = {
    "extend_dimensions": 0.1,
    "identify_key_concepts": 0.1,
    "parameterize": 0.1,
    "scale_complexity": 0.1,
}

GENERAL_TYPE = ["do_request"]


class DummyRetriever:
    def __init__(self, value):
        self.value = value

    def __call__(self):
        return self.value

    def values(self):
        return [self.value]


class RandomRetriever:
    def __init__(self, msg_value: dict, logger, curriculum_agent_lock, ckpt_dir):
        self.msg_value = msg_value
        self.logger = logger
        self.curriculum_agent_lock = curriculum_agent_lock
        self.completed_tasks = []
        self.complete_task_path = f"{ckpt_dir}/curriculum/completed_tasks.json"
        self.active_manager_task_name = None

    def _update_completed(self):
        with self.curriculum_agent_lock:
            self.completed_tasks = U.load_json(self.complete_task_path)

        self.completed_tasks = [U.problem_id(x) for x in self.completed_tasks]

        self.msg_value = {
            x: self.msg_value[x]
            for x in self.msg_value
            if x not in self.completed_tasks
        }

    def __call__(self):
        # Prune the skill managers of any tasks that are already complete
        self._update_completed

        # Randomly sample a skill manager from the rest to be evolved
        msg, value = random.sample(self.msg_value.items(), k=1)[0]
        self.logger.info(f"Randomly selected {msg} SkillManager")
        self.active_manager_task_name = msg
        return value

    def values(self):
        return self.msg_value.values()


class Evolver:

    def __init__(
        self,
        rank,
        isabelle_path,
        ckpt_dir,
        server_port,
        data_split="valid",
        skill_manager_lock=U.WithEmpty(),
        model_name="gpt-4",
        base_url: Optional[str]=None,
        temperature=0.7,
        chroma_bridge: ChromaBridge = None,  # type: ignore
        miniF2F_tasks: mp.Queue = None,  # type: ignore
        isolate: bool = False,
        isolate_v2: bool = False,
        curriculum_agent_lock=U.WithEmpty(),
        alternative_theorems_list: list[str | os.PathLike] | None = None,
        data_directory: str | os.PathLike | None = None,  # Only needed to fix isolate
        end_time: datetime | None = None,
        max_calls_per_s: int | None = None,
        evolve_prompt_dir: str = "lego_prover/prompts/skill_evolver",
        model_tokenizer_name: str | None = None,
    ) -> None:
        """
        A class representing an evolver for the LEGO Prover system.

        Args:
            rank (int): The rank of the evolver.
            isabelle_path (str): The path to the Isabelle installation.
            ckpt_dir (str): The directory to save checkpoints.
            server_port (int): The port number for the Isabelle server.
            data_split (str, optional): The data split to use. Defaults to "valid".
            skill_manager_lock (Any, optional): A lock for the skill manager. Defaults to U.WithEmpty().
            model_name (str, optional): The name of the language model to use. Defaults to "gpt-4".
            temperature (float, optional): The temperature for the language model. Defaults to 0.7.
            chroma_bridge (ChromaBridge): A bridge to the Chroma system. Defaults to None.
        """
        if isolate:
            assert (
                data_directory is not None
            ), "need directory of problem files to fix evolver behaviour"

        self.isolate = isolate
        self.isolate_v2 = isolate_v2

        if isolate_v2:
            assert isolate, "must set isolate flag if setting isolate_v2"

        self.evolve_prompt_dir = evolve_prompt_dir

        self.end_time = (
            end_time if end_time is not None else datetime.now() + timedelta(days=30)
        )

        self.data_directory = data_directory

        self.logger = logging.getLogger(f"evolver-{rank}")
        self.ckpt_dir = ckpt_dir
        self.skill_manager_lock = skill_manager_lock
        self.data_split = data_split

        self.miniF2F_tasks = miniF2F_tasks
        assert miniF2F_tasks is not None

        self.llm = LLMMixture(
            model_name=model_name,
            base_url=base_url,
            temperature=temperature,
            request_timeout=16000,
            max_calls_per_s=max_calls_per_s,
            logger=self.logger,
            usage_log=(ckpt_dir, 'usage_evolver'),
            model_tokenizer_name=model_tokenizer_name,
        )

        self.env = IsabelleEnv(
            logger=self.logger, isabelle_path=isabelle_path, server_port=server_port
        )
        self.env.reset()

        self.skill_manager = None  # Will be overwritten later on
        if not isolate:
            assert isinstance(chroma_bridge, ChromaBridge)
            self.skill_managers = DummyRetriever(
                SkillManager(
                    rank=rank,
                    logger=self.logger,
                    ckpt_dir=ckpt_dir,
                    skill_manager_lock=skill_manager_lock,
                    chroma_bridge=chroma_bridge,
                    alternative_theorems_list=alternative_theorems_list,
                )
            )
        else:
            assert isinstance(chroma_bridge, dict)
            self.skill_managers = RandomRetriever(
                msg_value={
                    pn: SkillManager(
                        rank=rank,
                        logger=self.logger,
                        ckpt_dir=os.path.join(ckpt_dir, pn),
                        skill_manager_lock=skill_manager_lock,
                        chroma_bridge=cb,
                        alternative_theorems_list=alternative_theorems_list,
                    )
                    for (pn, cb) in chroma_bridge.items()
                },
                logger=self.logger,
                curriculum_agent_lock=curriculum_agent_lock,
                ckpt_dir=ckpt_dir,
            )

        with skill_manager_lock:
            for skill_manager in self.skill_managers.values():
                skill_manager.sync_checkpoint()

    def _do_request(self, request_statement, skills, n_attempts=3):
        provenance = Provenance(
            creating_process="evolver_request",
            creating_task=request_statement,
            inputs=[request_statement] + list(skills),
        )

        skill_text = []
        for skill in skills:
            statement = self.env.get_marker_statement(skill)
            if statement is None:
                print(f"Warning! Malformed skill:\n{skill}")
                with open('WARNINGS.txt', 'a') as outfile:
                    print(f"=========================\n{datetime.now()}\nWarning! Malformed skill:\n{skill}\n\n", file=outfile)
                continue 

            exp = f"""# Statement
```isabelle
{statement}
```

# Proof
```isabelle
theory Scratch
  imports Complex_Main
begin

{skill}

end
```
"""
            skill_text.append(exp)
        skill_text = "\n\n####################\n\n".join(skill_text)

        template = U.load_text(f"lego_prover/prompts/skill_evolver/do_request.txt")
        system_message = SystemMessagePromptTemplate.from_template(template)
        system_message = system_message.format(
            examples=skill_text, formal_statement=request_statement
        )

        self.logger.info(
            f"****do_request evolver system message****\n{system_message.content}"
        )

        result_codes = []
        try:
            ai_messages = self.llm(
                [system_message], temperature=0.7, max_tokens=1024, n=n_attempts
            )
            for ai_message in ai_messages:
                self.logger.info(
                    f"****do_request evolver ai message****\n{ai_message.content}"
                )

                parsed_result = re.findall(
                    r"```isabelle(.*?)```", ai_message.content, re.DOTALL
                )
                if len(parsed_result) == 0:
                    self.logger.info("FAILURE TO PARSE RESULTS")
                    continue
                parsed_result = parsed_result[0]

                if len(parsed_result) > 0:
                    self.logger.info("Verifying with isabelle env...")
                    verified_result, _, result_code, _ = self.env.step(
                        code=parsed_result
                    )
                    self.logger.info(f"Success: {verified_result['success']}")
                    self.logger.info(f"Reason: {verified_result['reason']}")
                    result_codes.extend(result_code)
                else:
                    self.logger.info("FAILURE TO PARSE RESULTS")
        except Exception as e:
            self.logger.warn(f"do_request evolver error with: {str(e)}")
            self.logger.warn(f"Trace back:\n{traceback.format_exc()}")
            result_codes = []

        for _, full_code in result_codes:
            self.logger.info(f"Result code {full_code}")

        assert all([len(x) == 2 for x in result_codes])
        result_codes = [(x[0], x[1], provenance) for x in result_codes]

        return result_codes

    def _directed_evolve(self, problems, code, evolve_type, n_attempts=3):
        # "examples" are not learned, so not bothering to log them
        provenance = Provenance(
            creating_process=f"evolver_directed_{evolve_type}",
            creating_task=None,
            inputs=problems + [code],
        )

        problem_text = []
        for ix, problem in enumerate(problems):
            problem_text.append(f"#### problem {ix + 1} ####\n{problem}")
        problem_text = "\n\n".join(problem_text)

        if "theory" not in code:
            code = f"theory Scratch\n  imports Complex_Main\nbegin\n\n{code}\n\nend\n"

        with open(f"data/evolver_examples/{evolve_type}.txt", "r") as f:
            text = f.read()
        ori_examples = [e.strip() for e in text.split("<split>")]

        examples = random.sample(ori_examples, min(3, len(ori_examples)))
        random.shuffle(examples)

        examples = "\n\n####################\n\n".join(examples)

        template = U.load_text(
            os.path.join(self.evolve_prompt_dir, evolve_type + ".txt")
        )
        system_message = SystemMessagePromptTemplate.from_template(template)
        system_message = system_message.format(
            problems=problem_text, examples=examples, code=code
        )

        self.logger.info(
            f"****{evolve_type} evolver system message****\n{system_message.content}"
        )

        result_codes = []
        try:
            ai_messages = self.llm(
                [system_message], temperature=0.7, max_tokens=1024, n=n_attempts
            )
            for ai_message in ai_messages:
                self.logger.info(
                    f"****{evolve_type} evolver ai message****\n{ai_message.content}"
                )
                text = ai_message.content

                parsed_result = re.findall(r"```isabelle(.*?)```", text, re.DOTALL)
                if len(parsed_result) == 0:
                    self.logger.info("FAILURE TO PARSE RESULTS")
                    continue
                parsed_result = parsed_result[0]
                if len(parsed_result) > 0:
                    self.logger.info("Verifying with isabelle env...")
                    if "theory" not in parsed_result:
                        parsed_result = f"theory Scratch\n  imports Complex_Main\nbegin\n\n{parsed_result}\n\nend\n"
                    verified_result, _, result_code, _ = self.env.step(
                        code=parsed_result
                    )
                    self.logger.info(f"Success: {verified_result['success']}")
                    self.logger.info(f"Reason: {verified_result['reason']}")
                    result_codes.extend(result_code)
                else:
                    self.logger.info("FAILURE TO PARSE RESULTS")
        except Exception as e:
            self.logger.warn(f"{evolve_type} evolver error with: {str(e)}")
            self.logger.warn(f"Trace back:\n{traceback.format_exc()}")
            result_codes = []

        for _, full_code in result_codes:
            self.logger.info(f"Result code {full_code}")

        assert all([len(x) == 2 for x in result_codes])
        result_codes = [(x[0], x[1], provenance) for x in result_codes]

        return result_codes

    def retrieve_problems(self, query):
        assert isinstance(self.skill_manager, SkillManager)

        if os.path.exists(f"{self.ckpt_dir}/curriculum/completed_tasks.json"):
            completed_problem = U.load_json(
                f"{self.ckpt_dir}/curriculum/completed_tasks.json"
            )
        else:
            completed_problem = []

        # Normal LEGO-Prover retrieval
        if not self.isolate_v2:
            k = 20
            self.logger.info(f"Evolver retrieving for {k} problems")
            with self.skill_manager_lock:
                data = (f"{self.data_split}_problem_query", {"query": query, "k": k})
                outputs = self.skill_manager.chroma_bridge.run_cmd(data)
                ret_problem_names = []
                if outputs["error"] is None:
                    ret_problem_names = outputs["output"]
            ret_problem_names = list(
                filter(lambda x: x not in completed_problem, ret_problem_names)
            )
            self.logger.info(f"Return with {len(ret_problem_names)} problems")

        # If isolated v2, then the only task that the evolver should work towards is the task
        # Corresponding to the currently retrieved skill manager.
        else:
            assert isinstance(self.skill_managers, RandomRetriever)
            self.logger.info(
                f"Isolated Evolver retrieving only the Skill Manager's problem\nShould be:{self.skill_managers.active_manager_task_name}"
            )
            assert isinstance(
                self.skill_managers.active_manager_task_name, str
            ), self.skill_managers.active_manager_task_name
            assert self.data_directory is not None
            ret_problem_names = [
                os.path.join(
                    self.data_directory,
                    f"{self.skill_managers.active_manager_task_name}.json",
                )
            ]
            assert os.path.exists(
                ret_problem_names[0]
            ), "Cannot find the task for this skill manager"

        k = min(len(self.skill_manager.skill_requests), 20)
        ret_request_names = []
        if k != 0:
            with self.skill_manager_lock:
                data = ("request_query", {"query": query, "k": k})
                outputs = self.skill_manager.chroma_bridge.run_cmd(data)
                if outputs["error"] is None:
                    ret_request_names = outputs["output"]
                self.skill_manager.sync_checkpoint()
            ret_request_names = list(
                filter(
                    lambda x: self.skill_manager.skill_requests[x]["problem_name"]
                    not in completed_problem,
                    ret_request_names,
                )
            )
            self.logger.info(f"Return with {len(ret_request_names)} requests")

        problem_statements = []
        for problem_name in ret_problem_names:
            if "imosl" in problem_name:
                continue
            try:
                context = U.load_json(problem_name)
            except FileNotFoundError:
                self.logger.warn(f"Unable to find {problem_name}, skipping file")
                continue
            problem_statements.append(context["formal_statement"])

        request_statement = [
            self.skill_manager.skill_requests[request_name]["formal_statement"]
            for request_name in ret_request_names
        ]
        statements = request_statement + problem_statements
        statements = random.sample(statements, min(4, len(statements)))

        return statements

    def evolve_single_skill(self, context):
        assert isinstance(self.skill_manager, SkillManager)

        if random.random() > 0.7:
            evolve_type = random.choice(list(EVOLVE_TYPES.keys()))
        else:
            evolve_type = random.choice(GENERAL_TYPE)

        if evolve_type in EVOLVE_TYPES:
            self.logger.info(
                f"\n\nEvolver starting EVOLVE_TYPES evolution, {evolve_type}"
            )
            marker = context["marker"]
            problems = self.retrieve_problems(marker)
            code = context["full_code"]
            result_code = self._directed_evolve(
                problems, code, evolve_type, n_attempts=3
            )
        elif evolve_type == "do_request":
            self.logger.info(f"\n\nEvolver starting do_request")
            if os.path.exists(f"{self.ckpt_dir}/curriculum/completed_tasks.json"):
                completed_problem = U.load_json(
                    f"{self.ckpt_dir}/curriculum/completed_tasks.json"
                )
            else:
                completed_problem = []
            with self.skill_manager_lock:
                self.skill_manager.sync_checkpoint()
            request_list = list(
                filter(
                    lambda x: x["problem_name"] not in completed_problem,
                    list(self.skill_manager.skill_requests.values()),
                )
            )
            if len(request_list) > 0:
                request_list = sorted(request_list, key=lambda x: x["update_count"])
                smallest_request_update_count = request_list[0]["update_count"]
                smallest_request_list = []
                for elem in request_list:
                    if elem["update_count"] == smallest_request_update_count:
                        smallest_request_list.append(elem)
                    else:
                        break
                request = random.choice(smallest_request_list)
                skills = self.skill_manager.retrieve_skills(
                    request["formal_statement"], 5
                )
                skills = [skill["code"] for skill in skills]
                skills = random.sample(skills, 3)
                result_code = self._do_request(
                    request["formal_statement"], skills, n_attempts=3
                )
                self.skill_manager.update_count_request(request["request_name"])
            else:
                result_code = []
        else:
            raise NotImplementedError

        if len(result_code) > 10:
            self.logger.warn(
                f"Result code is too much! with {len(result_code)} result codes"
            )

        for mk, full_code, provenance in result_code:
            skill_full_code = (
                f"""theory Scratch\n  imports Complex_Main\nbegin\n\n{full_code}\nend"""
            )
            result, *_ = self.env.step(skill_full_code, quick_check=True)
            if result is True:
                skill_name = self.env.get_lemma_name(mk)
                origin = context["skill_name"]
                if evolve_type == "do_request":
                    origin = "do_request"
                self.logger.info(f"adding skill {full_code}")
                self.skill_manager.add_new_skill(
                    skill_name=skill_name,
                    description="-",
                    marker=mk,
                    full_code=full_code,
                    provenance=provenance,
                    origin=origin,
                )

    def evolve(self):
        consecutive_failures = 0

        # continue evolving for as long as there are problems to be solved.
        while self.miniF2F_tasks.qsize() > 0 and datetime.now() < self.end_time:
            try:
                # Select the skill manager to evolve
                self.skill_manager = self.skill_managers()

                with self.skill_manager_lock:
                    self.skill_manager.sync_checkpoint()
                skill_list = sorted(
                    self.skill_manager.skills.values(), key=lambda x: x["update_count"]
                )
                smallest_skill_update_count = skill_list[0]["update_count"]
                smallest_skill_list = []
                for elem in skill_list:
                    if elem["update_count"] == smallest_skill_update_count:
                        smallest_skill_list.append(elem)
                    else:
                        break
                skill = random.choice(smallest_skill_list)
                self.evolve_single_skill(skill)
                consecutive_failures = 0
            except Exception as e:
                consecutive_failures += 1
                self.logger.warning("Your last round rollout terminated due to error:")
                self.logger.warning(f"{e}\n{traceback.format_exc()}")
                print("Your last round rollout terminated due to error:")
                print(f"{e}\n{traceback.format_exc()}")
                if consecutive_failures >= 6:
                    raise
                self.env.reset(hard_reset=True)
                sleep(60)  # wait for prior programme to init

        if self.miniF2F_tasks.qsize() == 0:
            self.logger.info("miniF2F_tasks queue is empty; halting evolver.")
        else:
            self.logger.info("max job duration exceeded; halting evolver.")
