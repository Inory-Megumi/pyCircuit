# ruff: noqa: F823, F841 -- Module state captured by Rules is compiler-owned.
"""Concrete owned-state components with an explicit external FIFO protocol."""

import pycircuit as ac


@ac.struct
class BufferOutput:
    ready: ac.u1
    valid: ac.u1
    data: ac.u8


@ac.module
def Register8(write: ac.u1, data: ac.u8) -> ac.u8:  # noqa: N802
    stored: ac.u8 = 0

    @ac.rule(guard=lambda: write)
    def update() -> None:
        stored = data

    return stored


@ac.module
def Counter3(increment: ac.u1, decrement: ac.u1) -> ac.u3:  # noqa: N802
    count: ac.u3 = 0

    @ac.rule(guard=lambda: increment & (count < 5))
    def add() -> None:
        count = count + 1

    @ac.rule(guard=lambda: decrement & (count > 0))
    def subtract() -> None:
        count = count - 1

    ac.schedule(add, subtract)
    return count


@ac.module
def Slot8(put: ac.u1, data: ac.u8, take: ac.u1) -> BufferOutput:  # noqa: N802
    occupied: ac.u1 = 0
    stored: ac.u8 = 0

    @ac.rule(guard=lambda: take & occupied)
    def consume() -> None:
        occupied = 0

    @ac.rule(guard=lambda: put & ~occupied)
    def enqueue() -> None:
        stored = data
        occupied = 1

    ac.schedule(consume, enqueue)
    return BufferOutput(
        ready=~occupied | take,
        valid=occupied,
        data=stored if occupied else 0,
    )


@ac.module
def Fifo2x8(put: ac.u1, data: ac.u8, take: ac.u1) -> BufferOutput:  # noqa: N802
    count: ac.u2 = 0
    head: ac.u8 = 0
    tail: ac.u8 = 0

    @ac.rule(guard=lambda: take & (count > 0))
    def consume() -> None:
        head = tail
        count = count - 1

    @ac.rule(guard=lambda: put & (count == 1))
    def enqueue_tail() -> None:
        tail = data
        count = count + 1

    @ac.rule(guard=lambda: put & (count == 0))
    def enqueue_head() -> None:
        head = data
        count = count + 1

    # Test the occupied destination before the empty destination so one request
    # adds exactly one token. Consuming first permits replacement when full.
    ac.schedule(consume, enqueue_tail, enqueue_head)
    return BufferOutput(
        ready=(count < 2) | (take & (count > 0)),
        valid=count > 0,
        data=head if count > 0 else 0,
    )
