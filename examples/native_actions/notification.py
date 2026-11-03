# ruff: noqa: F823 -- persistent hardware state is captured, never executed.
import pycircuit as ac


@ac.struct
class Packet:
    tag: ac.u8
    data: ac.u8


@ac.module
def Cell():  # noqa: N802 -- hardware Module.
    stored: Packet = Packet(tag=0, data=0)
    ticks: ac.u8 = 0

    @ac.method(kind="action")
    def write(payload: Packet) -> None:
        pass

    @ac.rule
    def update() -> None:
        if write.active:
            stored = write.args.payload

    @ac.rule
    def tick() -> None:
        ticks = ticks + 1

    @ac.method(kind="query")
    def state() -> tuple[Packet, ac.u8]:
        return stored, ticks
