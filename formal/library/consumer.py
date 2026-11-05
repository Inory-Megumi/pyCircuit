# ruff: noqa: F823, F841 -- Module state captured by Rules is compiler-owned.
"""Reuse the published library with boundary, stall, replacement and drain traffic."""

import pycircuit as ac
from checks.basic import Counter3, Fifo2x8, Register8, Slot8


@ac.system
def ExerciseLibrary():  # noqa: N802
    phase: ac.u8 = 0
    put = (phase < 6) | (phase == 8)
    take = (
        (phase == 0)
        | (phase == 3)
        | (phase == 4)
        | (phase == 6)
        | (phase == 7)
        | (phase == 9)
        | (phase == 10)
    )
    data = phase + 10
    stored = Register8(put, data)
    count = Counter3(put, take)
    slot = Slot8(put, data, take)
    fifo = Fifo2x8(put, data, take)

    @ac.rule
    def observe() -> None:
        ac.log(
            "info",
            "library sample",
            phase,
            put,
            data,
            take,
            stored,
            count,
            slot.ready,
            slot.valid,
            slot.data,
            fifo.ready,
            fifo.valid,
            fifo.data,
        )

    @ac.rule
    def tick() -> None:
        phase = phase + 1
