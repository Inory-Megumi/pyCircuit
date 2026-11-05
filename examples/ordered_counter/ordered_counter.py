# ruff: noqa: F823 -- Module state captured by Rules is compiler-owned.
from pycircuit import bits, log, module, rule, schedule, system


@module
def OrderedCounter() -> bits[8]:  # noqa: N802
    count: bits[8] = 3

    @rule
    def increment() -> None:
        count = count + 1

    @rule
    def double() -> None:
        count = count * 2

    schedule(increment, double)
    return count


@system
def ExerciseOrderedCounter():  # noqa: N802
    value = OrderedCounter()

    @rule
    def observe() -> None:
        log("info", "ordered count", value)
