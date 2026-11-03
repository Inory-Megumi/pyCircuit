# ruff: noqa: F823 -- persistent hardware state is captured, never executed.
import pycircuit as ac
from native_demo.notification import Cell, Packet


@ac.system
def Exercise():  # noqa: N802 -- hardware System.
    left = Cell()
    right = Cell()
    phase: ac.u8 = 0
    choice = phase[:1]

    @ac.rule
    def next_phase() -> None:
        phase = phase + 1

    @ac.rule
    def even() -> None:
        if not choice:
            packet = Packet(tag=phase, data=phase + 10)
            left.write(packet)
            packet = Packet(tag=phase, data=phase + 20)
            right.write(packet)
            packet = Packet(tag=99, data=99)
            ac.guard(phase != 2)

    @ac.rule
    def odd() -> None:
        if choice:
            left.write(Packet(tag=phase, data=phase + 20))
            right.write(Packet(tag=phase, data=phase + 10))
            ac.guard(phase != 2)

    @ac.rule
    def observe() -> None:
        left_packet, left_ticks = left.state()
        right_packet, right_ticks = right.state()
        ac.log(
            "info",
            "cells",
            left_packet.tag,
            left_packet.data,
            right_packet.tag,
            right_packet.data,
            left_ticks,
            right_ticks,
        )
