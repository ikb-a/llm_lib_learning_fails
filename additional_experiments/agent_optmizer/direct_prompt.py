# This file has been modified from the original.

import copy
import json
import os
from typing import Any, Callable, Dict, List, Literal, Optional, Tuple, Union

from openai import BadRequestError

import autogen
from autogen.agentchat import Agent
#from autogen.agentchat.contrib.math_user_proxy_agent import MathUserProxyAgent as MUPA
from mupa import MathUserProxyAgent as MUPA
from autogen.code_utils import extract_code
from autogen.math_utils import get_answer
from aa import AssistantAgent

os.environ['AUTOGEN_USE_DOCKER'] = "False"  


def add_usages(accumulator: Optional[dict], usage: dict) -> dict:
    accumulator = copy.copy(accumulator)  # Shallowcopy OK

    if usage is None:
        print("WARNING: usage is None!")
        return accumulator
    
    if accumulator is None:
            return usage
    
    assert set(accumulator.keys()) == set(usage.keys())

    keys = list(accumulator.keys())
    for key in keys:
        if isinstance(accumulator[key], dict):
            accumulator[key] = add_usages(accumulator[key], usage[key])
        else:
            accumulator[key] += usage[key]
    return accumulator




#===============================

def is_termination_msg_mathchat(message):
    """Check if a message is a termination message."""
    if isinstance(message, dict):
        message = message.get("content")
        if message is None:
            return False
    cb = extract_code(message)
    contain_code = False
    for c in cb:
        if c[0] == "python":
            contain_code = True
            break
    if message.rstrip().find("TERMINATE") >= 0:
        return True
    return not contain_code and get_answer(message) is not None and get_answer(message) != ""


class MathUserProxyAgent(MUPA):
    MAX_CONSECUTIVE_AUTO_REPLY = 15
    DEFAULT_REPLY = "Continue. Please keep solving the problem until you need to query. (If you get to the answer, put it in \\boxed{}.)"
    PROMPTS = """Let's solve a math problem.
Query requirements:
You should always use the 'print' function for the output and use fractions/radical forms instead of decimals.
You can use packages like sympy to help you.
You must follow the formats below to write your code:
```python
# your code
```
If some packages are missing, you could also suggest a code to install the corresponding package.

Please follow this process:
1. Solve the problem step by step (do not over-divide the steps).
2. Take out any queries that can be asked through Python code (for example, any calculations or equations that can be calculated) and functions you know in the context of this conversation.

Please
(1) do not mix suggested Python codes and function calls in one step.
(2) You MUST remember that you don’t have a function named "python" available.

You must follow the formats below to write your Python code:
```python
# your code
```

3. Wait for me to give the results or wait for the executed results of the function call.
4. Continue if you think the result is correct. If the result is invalid or unexpected, please correct your query or reasoning.

After all the queries are run and you get the answer, put the answer in \\boxed{}.

Problem:
"""

    def __init__(
        self,
        name: Optional[str] = "MathChatAgent",
        is_termination_msg: Optional[Callable[[Dict], bool]] = is_termination_msg_mathchat,
        human_input_mode: Literal["ALWAYS", "NEVER", "TERMINATE"] = "NEVER",
        default_auto_reply: Optional[Union[str, Dict, None]] = DEFAULT_REPLY,
        max_invalid_q_per_step=3,
        **kwargs: Any,
    ):
        super().__init__(
            name=name,
            is_termination_msg=is_termination_msg,
            human_input_mode=human_input_mode,
            default_auto_reply=default_auto_reply,
            max_invalid_q_per_step=max_invalid_q_per_step,
            **kwargs,
        )
        del self._reply_func_list[2]
        self.register_reply([Agent, None], MathUserProxyAgent._generate_math_reply, position=4)
        del self._reply_func_list[3]
        self.register_reply(
            trigger=autogen.ConversableAgent, reply_func=MathUserProxyAgent.generate_function_call_reply, position=3
        )
        self.register_reply(
            trigger=autogen.ConversableAgent, reply_func=MathUserProxyAgent._check_final_result, position=0
        )

        self.max_function_call_trial = 3
        self.query = None
        self.answer = None
        self.is_correct = None

    def generate_function_call_reply(
        self,
        messages: Optional[List[Dict]] = None,
        sender: Optional[autogen.ConversableAgent] = None,
        config: Optional[Any] = None,
    ) -> Tuple[bool, Union[Dict, None]]:
        """Generate a reply using function call."""
        if messages is None:
            messages = self._oai_messages[sender]
        message = messages[-1]
        if "function_call" in message:
            is_exec_success, func_return = self.execute_function(message["function_call"])
            if is_exec_success:
                self.max_function_call_trial = 3
                return True, func_return
            else:
                if self.max_function_call_trial == 0:
                    error_message = func_return["content"]
                    self.max_function_call_trial = 3
                    return (
                        True,
                        "The func is executed failed many times. "
                        + error_message
                        + ". Please directly reply me with TERMINATE. We need to terminate the conversation.",
                    )
                else:
                    revise_prompt = "You may make a wrong function call (It may due the arguments you provided doesn't fit the function arguments like missing required positional argument). \
                    If you think this error occurs due to you make a wrong function arguments input and you could make it success, please try to call this function again using the correct arguments. \
                    Otherwise, the error may be caused by the function itself. Please directly reply me with TERMINATE. We need to terminate the conversation. "
                    error_message = func_return["content"]
                    return True, "The func is executed failed." + error_message + revise_prompt
        return False, None

    def initiate_chat(
        self,
        recipient,
        answer: None,
        silent: Optional[bool] = False,
        **context,
    ):
        self.query = context["problem"]
        if not isinstance(answer, str):
            answer = str(answer)
            if answer.endswith(".0"):
                answer = answer[:-2]
            self._answer = answer
        else:
            self._answer = answer

        self.is_correct = None

        self._prepare_chat(recipient, True)
        error_message = None
        try:
            prompt = self.PROMPTS + context["problem"]
            self.send(prompt, recipient, silent=silent)
        except BadRequestError as e:
            error_message = str(e)
            self.is_correct = 0
            print(f"error information: {error_message}")


        total_usage = recipient.get_total_usage()
        actual_usage = recipient.get_actual_usage()
        recipient.print_usage_summary()
        recipient.reset()
        is_correct = copy.deepcopy(self.is_correct)
        self._reset()
        return is_correct, actual_usage, total_usage

    def _check_final_result(
        self,
        messages: Optional[List[Dict]] = None,
        sender: Optional[autogen.Agent] = None,
        config: Optional[Any] = None,
    ):
        messages = messages[-1]
        if isinstance(messages, dict):
            messages = messages.get("content")
            if messages is None:
                return False, None

        cb = extract_code(messages)
        contain_code = False
        for c in cb:
            if c[0] == "python":
                contain_code = True
                break
        if not contain_code and get_answer(messages) is not None and get_answer(messages) != "":
            if get_answer(messages) == self._answer:
                self.is_correct = 1
                return True, "The result is Correct. Please reply me with TERMINATE."
            else:
                self.is_correct = 0
                return False, None
        else:
            return False, None

    def _reset(self):
        super()._reset()
        self.max_function_call_trial = 3
        self.is_correct = None
        self.query = None
        self.answer = None



def main(dataset_name: str, output_dir: str | os.PathLike, model_name: str, LIMIT: Optional[int], run_id) -> None:

    accumulated_actual_usage = None 
    accumulated_total_usage = None


    # =================================================
    # LOAD DATASET
    # 
    # https://proceedings.mlr.press/v235/zhang24cd.html
    # For each data type (7 in total), we randomly 
    # choose 20 test examples and 80 training examples, 
    # and report the accuracy of each data type respectively.
    test_data = []
    with open(f"MATH/subset/{dataset_name}.jsonl", encoding="utf-8") as f:
        for line in f:
            test_data.append(json.loads(line))

    if LIMIT is not None:
        test_data = test_data[0:LIMIT]
            
    print(f"# TEST QUESTIONS: {len(test_data)}")

    # ===================================
    # Agent construction
    from azure_key import AZURE_API_KEY, AZURE_API_VERSION, AZURE_ENDPOINT

    #llm_config = autogen.LLMConfig(
    llm_config = autogen.LLMConfig(
        config_list=[
            {
                "model": model_name, # "gpt-4o-mini", #"gpt-4-1106-preview",
                "api_type": "azure",
                "api_key": AZURE_API_KEY, #os.environ["AZURE_OPENAI_API_KEY"],
                "base_url": AZURE_ENDPOINT, #"https://ENDPOINT.openai.azure.com/",
                "api_version": AZURE_API_VERSION, # "2023-07-01-preview",
            }
        ]
    )

    with llm_config:
        assistant = AssistantAgent(
            name="assistant",
            system_message="You are a helpful assistant.",
        )

    user_proxy = MathUserProxyAgent(
        name="mathproxyagent",
        human_input_mode="NEVER",
        code_execution_config={"work_dir": os.path.join('_direct', dataset_name, f"_output{run_id}"), "use_docker": False},
    )

    #===========================================

    # Test without agent optimizations



    sum = 0
    results = {}
    for index, query in enumerate(test_data):
        print('\n'*5)
        print('='*50)
        print('='*50)
        print(f'BEGIN EVAL PROBLEM #{index}')
        print('='*50)
        print(query['question'])
        print('='*50)
        print(f'True Answer: {query["answer"]}')
        print('='*50)
        print('='*50)
        results = {'index': index}

        is_correct, actual_usage, total_usage = user_proxy.initiate_chat(recipient=assistant, answer=query["answer"], problem=query["question"])
        if is_correct is None:
            is_correct = False 
            print("WARNING WARNING WARNING: Correctness could not be determined, setting to false. Too many auto-turns shut-down?")
        print(is_correct)
        sum += is_correct

        results['is_correct'] = is_correct

        with open(os.path.join(args.output_dir, 'results.jsonl'), 'a') as f:
            print(json.dumps(results), file=f)

        accumulated_actual_usage = add_usages(accumulator=accumulated_actual_usage, usage=actual_usage)
        accumulated_total_usage = add_usages(accumulator=accumulated_total_usage, usage=total_usage)

    success_rate_without_agent_training = sum / len(test_data)

    print(f'Direct System, Correct: {sum}/{len(test_data)} = {100*success_rate_without_agent_training:.2f}')

    print("ACUTAL USAGE:")
    print(json.dumps(accumulated_actual_usage, indent=2, sort_keys=True))
    with open(os.path.join(output_dir, 'test_time_actual_usage.json'), 'w') as f:
        json.dump(accumulated_actual_usage, f, indent=2, sort_keys=True)

    print()

    print("TOTAL_USAGE")
    print(json.dumps(accumulated_total_usage, indent=2, sort_keys=True))
    with open(os.path.join(output_dir, 'test_time_total_usage.json'), 'w') as f:
        json.dump(accumulated_total_usage, f, indent=2, sort_keys=True)


if __name__ == '__main__':
    import argparse
    from datetime import datetime 

    parser = argparse.ArgumentParser()
    parser.add_argument('--dataset', default='geometry', choices=['algebra', 'counting_and_probability', 'geometry', 'intermediate_algebra', 'number_theory', 'prealgebra', 'precalculus'])
    parser.add_argument('--output_dir', type=str, default=None)
    parser.add_argument('--model', type=str, default='gpt-4o-mini')
    parser.add_argument('--limit', type=int, default=None, help='Truncate dataset to this size')
    parser.add_argument('--run_id', type=str, default=None)
    #parser.add_argument('--verbose', action='store_true')

    args = parser.parse_args()

    if args.run_id is None:
        RUN_ID = f'{datetime.now()}'
    else:
        RUN_ID = args.run_id
    print("<RUN_ID>")
    print(RUN_ID)
    print("</RUN_ID>")
    print(args.dataset)

    if args.output_dir is None:
        args.output_dir = f'outputs_direct/{args.dataset}_{RUN_ID}/'
        os.makedirs(args.output_dir, exist_ok=False)
    else:
        os.makedirs(args.output_dir, exist_ok=False)

    with open(os.path.join(args.output_dir, 'RUN_ID.txt'), 'w') as f:
        print(RUN_ID, file=f, end='')
    with open(os.path.join(args.output_dir, 'arguments.txt'), 'w') as f:
        f.write(json.dumps(vars(args), indent=2, sort_keys=True))

    main(args.dataset, args.output_dir, args.model, args.limit, RUN_ID)


