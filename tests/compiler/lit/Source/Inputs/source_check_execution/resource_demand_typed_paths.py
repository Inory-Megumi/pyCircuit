# Captured state proposals and unused pop results are intentional DSL effects.
# ruff: noqa: F823, F841
from enum import Enum
import pycircuit as ac


@ac.encoding(width=1)
class Phase(Enum):
    EMPTY = 0
    BUSY = 1


@ac.struct
class Control:
    phase: Phase
    count: ac.u2


@ac.system
def Top():
    state: Control = Control(phase=Phase.EMPTY, count=0)
    other: Control = Control(phase=Phase.EMPTY, count=0)
    fifo = ac.queue[ac.u8](depth=2, latency=1)

    @ac.rule
    def first() -> None:
        if state.phase == Phase.EMPTY:
            fifo.push(11)

    @ac.rule
    def second() -> None:
        if state.phase == Phase.BUSY and state.count != 3:
            fifo.push(7)

    @ac.rule
    def take_first() -> None:
        if state.phase == Phase.EMPTY:
            value = fifo.pop()

    @ac.rule
    def take_second() -> None:
        if state.phase == Phase.BUSY:
            value = fifo.pop()

    @ac.rule
    def tick() -> None:
        state = Control(phase=Phase.BUSY if state.phase == Phase.EMPTY else Phase.EMPTY,
            count=state.count + 1)
        other = Control(phase=Phase.BUSY if other.phase == Phase.EMPTY else Phase.EMPTY,
            count=other.count + 1)
