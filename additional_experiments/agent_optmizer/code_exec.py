# This file has been modified from the original.

import logging
import os
import pathlib
import re
import string
import subprocess
import sys
import time
import venv
import concurrent.futures
from concurrent.futures import ThreadPoolExecutor, TimeoutError
from hashlib import md5
from types import SimpleNamespace
from typing import Callable, Optional, Union
from pathlib import Path 

import docker

SENTINEL = object()
DEFAULT_MODEL = "gpt-4"
FAST_MODEL = "gpt-3.5-turbo"
# Regular expression for finding a code block
# ```[ \t]*(\w+)?[ \t]*\r?\n(.*?)[ \t]*\r?\n``` Matches multi-line code blocks.
#   The [ \t]* matches the potential spaces before language name.
#   The (\w+)? matches the language, where the ? indicates it is optional.
#   The [ \t]* matches the potential spaces (not newlines) after language name.
#   The \r?\n makes sure there is a linebreak after ```.
#   The (.*?) matches the code itself (non-greedy).
#   The \r?\n makes sure there is a linebreak before ```.
#   The [ \t]* matches the potential spaces before closing ``` (the spec allows indentation).
CODE_BLOCK_PATTERN = r"```[ \t]*(\w+)?[ \t]*\r?\n(.*?)\r?\n[ \t]*```"
WORKING_DIR = os.path.join(os.path.dirname(os.path.realpath(__file__)), "extensions")
UNKNOWN = "unknown"
TIMEOUT_MSG = "Timeout"
DEFAULT_TIMEOUT = 600
WIN32 = sys.platform == "win32"
PATH_SEPARATOR = (WIN32 and "\\") or "/"
PYTHON_VARIANTS = ["python", "Python", "py"]

logger = logging.getLogger(__name__)


from autogen.code_utils import is_docker_running, in_docker_container, decide_use_docker, check_can_use_docker_or_throw, _sanitize_filename_for_docker_tag

FILE_REGEX = re.compile(r'File ".+?"')

def execute_code(
    code: str,
    timeout: int = 100,
    filename: Optional[str] = None,
    work_dir: Optional[str] = None,
    use_docker=False, 
    lang: Optional[str] = "python",
) -> tuple[int, str, Optional[str]]:
    assert not use_docker
    assert filename is None 
    
    work_dir_path = Path('.') if work_dir is None else Path(work_dir)

    if not work_dir_path.exists():
        os.makedirs(work_dir_path, exist_ok=True)

    code_hash = md5(code.encode()).hexdigest()
    # create a file with a automatically generated name
    exec_file = f"tmp_code_{code_hash}.{'py' if lang.startswith('python') else lang}"
    try:
        # write all code pieces into a file
        with open(work_dir_path/exec_file, 'w') as fw:
            fw.write(code)

        # execute code file
        result = subprocess.run(
            ['python', str((work_dir_path/exec_file).resolve())], 
            capture_output=True, 
            check=False, text=True,
            timeout=timeout,
        )
        if result.returncode != 0:  # execution failed
            error_msg = result.stderr.strip()
            error_msg = re.sub(FILE_REGEX, 'File ""', error_msg)
            
            os.remove(work_dir_path/exec_file)
            return result.returncode, error_msg, None
        else:  # execution success
            output = result.stdout.strip()
            os.remove(work_dir_path/exec_file)
            return 0, output, None
    except subprocess.TimeoutExpired:
        os.remove(work_dir_path/exec_file)
        return 1, TIMEOUT_MSG, None

def execute_code_BUGGY(
    code: Optional[str] = None,
    timeout: Optional[int] = None,
    filename: Optional[str] = None,
    work_dir: Optional[str] = None,
    use_docker: Union[list[str], str, bool] = SENTINEL,
    lang: Optional[str] = "python",
) -> tuple[int, str, Optional[str]]:
    """Execute code in a docker container.
    This function is not tested on MacOS.

    Args:
        code (Optional, str): The code to execute.
            If None, the code from the file specified by filename will be executed.
            Either code or filename must be provided.
        timeout (Optional, int): The maximum execution time in seconds.
            If None, a default timeout will be used. The default timeout is 600 seconds. On Windows, the timeout is not enforced when use_docker=False.
        filename (Optional, str): The file name to save the code or where the code is stored when `code` is None.
            If None, a file with a randomly generated name will be created.
            The randomly generated file will be deleted after execution.
            The file name must be a relative path. Relative paths are relative to the working directory.
        work_dir (Optional, str): The working directory for the code execution.
            If None, a default working directory will be used.
            The default working directory is the "extensions" directory under
            "path_to_autogen".
        use_docker (list, str or bool): The docker image to use for code execution.
            Default is True, which means the code will be executed in a docker container. A default list of images will be used.
            If a list or a str of image name(s) is provided, the code will be executed in a docker container
            with the first image successfully pulled.
            If False, the code will be executed in the current environment.
            Expected behaviour:
                - If `use_docker` is not set (i.e. left default to True) or is explicitly set to True and the docker package is available, the code will run in a Docker container.
                - If `use_docker` is not set (i.e. left default to True) or is explicitly set to True but the Docker package is missing or docker isn't running, an error will be raised.
                - If `use_docker` is explicitly set to False, the code will run natively.
            If the code is executed in the current environment,
            the code must be trusted.
        lang (Optional, str): The language of the code. Default is "python".

    Returns:
        int: 0 if the code executes successfully.
        str: The error message if the code fails to execute; the stdout otherwise.
        image: The docker image name after container run when docker is used.
    """
    if all((code is None, filename is None)):
        error_msg = f"Either {code=} or {filename=} must be provided."
        logger.error(error_msg)
        raise AssertionError(error_msg)

    running_inside_docker = in_docker_container()
    docker_running = is_docker_running()

    # SENTINEL is used to indicate that the user did not explicitly set the argument
    if use_docker is SENTINEL:
        use_docker = decide_use_docker(use_docker=None)
    check_can_use_docker_or_throw(use_docker)

    timeout = timeout or DEFAULT_TIMEOUT
    original_filename = filename
    if WIN32 and lang in ["sh", "shell"] and (not use_docker):
        lang = "ps1"
    if filename is None:
        code_hash = md5(code.encode()).hexdigest()
        # create a file with a automatically generated name
        filename = f"tmp_code_{code_hash}.{'py' if lang.startswith('python') else lang}"
    if work_dir is None:
        work_dir = WORKING_DIR

    filepath = os.path.join(work_dir, filename)
    file_dir = os.path.dirname(filepath)
    os.makedirs(file_dir, exist_ok=True)

    if code is not None:
        with open(filepath, "w", encoding="utf-8") as fout:
            fout.write(code)

    if not use_docker or running_inside_docker:
        # already running in a docker container
        cmd = [
            sys.executable if lang.startswith("python") else _cmd(lang),
            f".\\{filename}" if WIN32 else filename,
        ]
        with ThreadPoolExecutor(max_workers=1) as executor:
            future = executor.submit(
                subprocess.run,
                cmd,
                cwd=work_dir,
                capture_output=True,
                text=True,
            )
            try:
                result = future.result(timeout=timeout)
                #executor.shutdown(wait=False)
            except TimeoutError:
                #executor.shutdown(wait=False)
                if original_filename is None:
                    os.remove(filepath)

                # https://stackoverflow.com/questions/48350257/how-to-exit-a-script-after-threadpoolexecutor-has-timed-out 
                import atexit
                atexit.unregister(concurrent.futures.thread._python_exit)
                executor.shutdown = lambda wait:None

                return 1, TIMEOUT_MSG, None
        if original_filename is None:
            os.remove(filepath)
        if result.returncode:
            logs = result.stderr
            if original_filename is None:
                abs_path = str(pathlib.Path(filepath).absolute())
                logs = logs.replace(str(abs_path), "").replace(filename, "")
            else:
                abs_path = str(pathlib.Path(work_dir).absolute()) + PATH_SEPARATOR
                logs = logs.replace(str(abs_path), "")
        else:
            logs = result.stdout
        return result.returncode, logs, None

    # create a docker client
    if use_docker and not docker_running:
        raise RuntimeError(
            "Docker package is missing or docker is not running. Please make sure docker is running or set use_docker=False."
        )

    client = docker.from_env()

    image_list = (
        ["python:3-slim", "python:3", "python:3-windowsservercore"]
        if use_docker is True
        else [use_docker]
        if isinstance(use_docker, str)
        else use_docker
    )
    for image in image_list:
        # check if the image exists
        try:
            client.images.get(image)
            break
        except docker.errors.ImageNotFound:
            # pull the image
            print("Pulling image", image)
            try:
                client.images.pull(image)
                break
            except docker.errors.DockerException:
                print("Failed to pull image", image)
    # get a randomized str based on current time to wrap the exit code
    exit_code_str = f"exitcode{time.time()}"
    abs_path = pathlib.Path(work_dir).absolute()
    cmd = [
        "sh",
        "-c",
        f'{_cmd(lang)} "{filename}"; exit_code=$?; echo -n {exit_code_str}; echo -n $exit_code; echo {exit_code_str}',
    ]
    # create a docker container
    container = client.containers.run(
        image,
        command=cmd,
        working_dir="/workspace",
        detach=True,
        # get absolute path to the working directory
        volumes={abs_path: {"bind": "/workspace", "mode": "rw"}},
    )
    start_time = time.time()
    while container.status != "exited" and time.time() - start_time < timeout:
        # Reload the container object
        container.reload()
    if container.status != "exited":
        container.stop()
        container.remove()
        if original_filename is None:
            os.remove(filepath)
        return 1, TIMEOUT_MSG, image
    # get the container logs
    logs = container.logs().decode("utf-8").rstrip()
    # commit the image
    tag = _sanitize_filename_for_docker_tag(filename)
    container.commit(repository="python", tag=tag)
    # remove the container
    container.remove()
    # check if the code executed successfully
    exit_code = container.attrs["State"]["ExitCode"]
    if exit_code == 0:
        # extract the exit code from the logs
        pattern = re.compile(f"{exit_code_str}(\\d+){exit_code_str}")
        match = pattern.search(logs)
        exit_code = 1 if match is None else int(match.group(1))
        # remove the exit code from the logs
        logs = logs if match is None else pattern.sub("", logs)

    if original_filename is None:
        os.remove(filepath)
    if exit_code:
        logs = logs.replace(f"/workspace/{filename if original_filename is None else ''}", "")
    # return the exit code, logs and image
    return exit_code, logs, f"python:{tag}"


if __name__ == '__main__':
    print("RUN CODE")
    execute_code("import time;time.sleep(999)", timeout=1, filename='tempymctempface.py', use_docker=False)
    print("DONE")