"""An elastic FIFO buffer using the standard Queue contract."""

import pycircuit as ac


@ac.module
# Module and static parameter names follow native hardware conventions.
def Pipe(*, Width: int = 8, Depth: int = 1):  # noqa: N802, N803
    tokens = ac.queue[ac.bits[Width]](
        depth=Depth, latency=1, ready_policy="downstream_pop"
    )

    @ac.method
    def push(value: ac.bits[Width]) -> None:
        tokens.push(value)

    @ac.method
    def pop() -> ac.bits[Width]:
        return tokens.pop()

    @ac.method(kind="query")
    def peek() -> ac.bits[Width]:
        return tokens.peek()
