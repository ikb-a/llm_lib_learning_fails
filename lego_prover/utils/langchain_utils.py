from __future__ import annotations
import random
import time
import traceback

from langchain.schema import (
    LLMResult,
    AIMessage,
    HumanMessage,
    SystemMessage,
    ChatGeneration,
)

#from azure_key import AZURE_API_KEY, AZURE_API_VERSION, AZURE_ENDPOINT,OPENAI_KEY
from azure_key import OPENAI_KEY

import os

from typing import List, Optional, Any

import numpy as np
import openai
import tiktoken
from tokenizers import Tokenizer
import traceback
import json 
from lego_prover.utils import RateLimitedCall


REASONING_MODELS_o3 = ["o3-mini"]


class LLMMixture:
    def __init__(
        self, 
        model_name, 
        base_url: Optional[str],
        temperature, 
        request_timeout, 
        max_calls_per_s, 
        logger,
        usage_log: Optional[tuple[str, str]],
        model_tokenizer_name: str = None,
    ) -> None:
        self.usage_log = None 
        if usage_log is not None:
            assert len(usage_log) == 2  # (log path, description)
            self.usage_log = os.path.join(usage_log[0], usage_log[1])
            os.makedirs(self.usage_log, exist_ok=True)

        if base_url is None:
            self.encoder = tiktoken.encoding_for_model(model_name=model_name)
        else:
            assert model_tokenizer_name is not None 
            self.encoder = Tokenizer.from_pretrained(model_tokenizer_name)

        self.model_name = model_name
        self.base_url = base_url
        self.temperature = temperature
        self.request_timeout = request_timeout

        """
        self._client = openai.AzureOpenAI(
            azure_endpoint=AZURE_ENDPOINT,
            api_version=(
                AZURE_API_VERSION if model_name != "o3-mini" else "2024-12-01-preview"
            ),
            api_key=AZURE_API_KEY,
        )
        """
        open_ai_args = {'api_key': OPENAI_KEY, 'timeout': 1500} #  timeout=1500 CORRECT PLACE FOR TIMEOUT!!!
        if self.base_url is not None:
            open_ai_args['base_url'] = self.base_url

        self._client = openai.OpenAI(**open_ai_args)


        self.rate_limited_client = RateLimitedCall(
            call=self._client.chat.completions.create,
            calls_per_s=max_calls_per_s,
            logger=logger,
        )
        self.logger = logger

    def query(
        self, langchain_msgs, llm_type="short", n=1, temperature=None, max_tokens=None
    ):
        # Forcibly override for reasoning models; in effect o3-mini or Qwen3.
        if self.model_name in REASONING_MODELS_o3:
            max_tokens = 8192

        if 'Qwen3' in self.model_name:
            max_tokens = 32768 # 32768  # Based on https://huggingface.co/Qwen/Qwen3-32B

        success = False
        max_retry = 50
        messages = []
        for msg in langchain_msgs:
            if isinstance(msg, SystemMessage):
                messages.append({"role": "system", "content": msg.content})

                if self.model_name in REASONING_MODELS_o3:  # Note: Won't work for o1-mini
                    messages[-1]["role"] = "developer"

            if isinstance(msg, HumanMessage):
                messages.append({"role": "user", "content": msg.content})
        while max_retry > 0:
            try:
                if self.model_name not in ["gpt-4o-mini", "gpt-4o", "o3-mini", "Meta-Llama-3.1-8B-Instruct", "Qwen3-14B"]:
                    raise NotImplementedError(
                        "Only implemented for gpt-4o-mini, gpt-4o, o3-mini"
                    )
                # Do not need to worry about short vs. long context
                llm_model = self.model_name

                # print(f"ckpt in 1 {llm_type}, {llm_model}")
                if temperature is None:
                    temperature = self.temperature

                generation_params = {
                    "model": llm_model,
                    "messages": messages,
                    "temperature": temperature,
                    "n": n,
                    "max_tokens": max_tokens,
                }
                # override generation params for OpenAI reasoning model
                if self.model_name in REASONING_MODELS_o3:
                    generation_params = {
                        "model": llm_model,
                        "messages": messages,
                        "n": n,
                        "max_completion_tokens": max_tokens,
                        # Reasoning model does not support temperature
                        # Also, max_tokens renamed
                        # https://learn.microsoft.com/en-us/azure/ai-services/openai/how-to/reasoning?tabs=python-secure
                    }

                # response = self.client.chat.completions.create(
                response = self.rate_limited_client.call(**generation_params)
                self.logger.info(f'Call Complete. Token Usage: {response.usage}')
                if self.usage_log is not None:
                    with open(os.path.join(self.usage_log, f'{os.getpid()}_{time.time()}.json'), 'w') as of:
                        json.dump(response.usage.model_dump(), of)


                # print("ckpt in 2")
            except openai.RateLimitError:
                print(".", end="", flush=True)
                time.sleep(0.1)
            except openai.APIConnectionError as e:
                time.sleep(random.randint(1, 30))
                max_retry -= 1
                print(f"==========================\nOpenai Connection err llmmixture: {e}\nRemaining retries: {max_retry}\n==========================", flush=True)
            except openai.APIError as e:
                time.sleep(random.randint(1, 30))
                if 'Bad gateway. {"error":{"code":502,"message":"Bad gateway."' in str(
                    e
                ) or "502: Bad gateway" in str(e):
                    print("-", end="", flush=True)
                else:
                    print(f"APIError了: {e}", flush=True)
                max_retry -= 1
            except Exception as e:
                time.sleep(random.randint(1, 30))
                print(f"Exception 了:{e}", flush=True)
                traceback.print_exc()
                max_retry -= 1
            else:
                success = True
                break
        if success:
            if n == 1:
                res = response.choices[0].message.content
                return res
            else:
                res = []
                for ix in range(n):
                    res.append(response.choices[ix].message.content)
                return res
        else:
            return ""

    def __call__(self, messages, temperature=None, max_tokens=1024, n=1) -> Any:
        if 'Qwen3' in self.model_name:
            max_tokens = 32768 # 32768  # Based on https://huggingface.co/Qwen/Qwen3-32B

        word_count = 0
        for msg in messages:
            word_count += len(self.encoder.encode(msg.content))

        if word_count < 3500:
            results = self.query(messages, "short", temperature=temperature, n=n, max_tokens=max_tokens)
        elif word_count < (16385 - 2100):
            results = self.query(
                messages,
                "long",
                temperature=temperature,
                max_tokens=max_tokens,
                n=n,
            )
        else:
            assert False, f"query too long, with {word_count} token in total"

        if n == 1:
            return AIMessage(content=results)
        else:
            ret_messages = []
            for res in results:
                ret_messages.append(AIMessage(content=res))
            return ret_messages

    """
    def generate(
        self, batch_message, slow_mode=False, temperature=None, max_tokens=1024
    ):
        if slow_mode is False:
            # print("ckpt 1")
            n = len(batch_message)
            word_count = 0
            messages = batch_message[0]
            for msg in messages:
                word_count += len(self.encoder.encode(msg.content))
            # print(f"ckpt 2 {word_count}")

            if word_count < 3500:
                results = self.query(
                    messages,
                    "short",
                    n=n,
                    temperature=temperature,
                    max_tokens=max_tokens,
                )
            elif word_count < 15000:
                results = self.query(
                    messages,
                    "long",
                    n=n,
                    temperature=temperature,
                    max_tokens=max_tokens,
                )
            else:
                assert False, f"query too long, with {word_count} token in total"

            generations = []
            for res in results:
                generations.append([ChatGeneration(message=AIMessage(content=res))])
            # print(f"Here successful with {len(results)}")
            return LLMResult(generations=generations)
        else:
            results = []
            for messages in batch_message:
                word_count = 0
                messages = batch_message[0]
                for msg in messages:
                    word_count += len(self.encoder.encode(msg.content))
                if word_count < 7000:
                    res = self.query(messages, "short")
                else:
                    res = self.query(messages, "long")
                results.append(res)
            generations = []
            for res in results:
                generations.append([ChatGeneration(text=res)])
            return LLMResult(generations=generations)
    """