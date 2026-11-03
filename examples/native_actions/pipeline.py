"""Three elastic stages; each transfer is one ordinary atomic Rule."""

# ruff: noqa: F823 -- persistent hardware state is captured, never executed.

import pycircuit as ac
from pycircuit.lib.pipe import Pipe


@ac.module
def Pipeline(  # noqa: N802 -- hardware Module.
    source_enable: ac.u1,
    sink_enable: ac.u1,
    *,
    Depth: int = 1,  # noqa: N803 -- static hardware parameter.
) -> tuple[ac.u8, ac.u8]:
    first = Pipe(Width=8, Depth=Depth)
    second = Pipe(Width=8, Depth=Depth)
    third = Pipe(Width=8, Depth=Depth)
    next_input: ac.u8 = 0
    count: ac.u8 = 0
    last: ac.u8 = 0

    @ac.rule
    def produce() -> None:
        if source_enable:
            first.push(next_input + 1)
            next_input = next_input + 1

    @ac.rule
    def double() -> None:
        value = first.pop()
        second.push(value + value)

    @ac.rule
    def transform() -> None:
        value = second.pop()
        third.push(value ^ 0x55)

    @ac.rule
    def consume() -> None:
        if sink_enable:
            last = third.pop()
            count = count + 1

    return last, count
