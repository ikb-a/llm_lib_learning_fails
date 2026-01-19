from typing import Callable
from datetime import datetime, timedelta
from time import sleep


class RateLimitedCall:
    """
    Prevents *succesful* calls to <call> from exceeding the rate provided.
    Calls that raise an error will not count towards the internal rate limit.
    (i.e., if a call goes through and raises an error, then the next attempt
    will go through immediately as enough time must have already passed if the
    previous call was allowed to be made)
    """

    def __init__(self, call: Callable, calls_per_s: float | None, logger=None) -> None:
        self._call = call
        self.wait_time = 1 / calls_per_s if calls_per_s is not None else 0
        self.last_succesful_call = datetime.now() - timedelta(
            seconds=self.wait_time + 1
        )
        self.logger = logger

    def call(self, *args, **kwargs):
        elapsed = datetime.now() - self.last_succesful_call

        remaining = self.wait_time - elapsed.total_seconds()
        if remaining > 0:
            if self.logger is not None:
                self.logger.info(f"Rate limiter activated for {remaining} seconds")
            sleep(remaining)

        result = self._call(*args, **kwargs)
        self.last_succesful_call = datetime.now()
        return result


if __name__ == "__main__":
    import random

    def tmp_fun(x):
        if random.randint(1, 6) == 6:
            print(datetime.now())
            return 1
        else:
            raise ZeroDivisionError

    test = RateLimitedCall(call=tmp_fun, calls_per_s=0.5)

    succ = 0
    while succ < 10:
        try:
            succ += test.call(succ)
        except ZeroDivisionError:
            pass
