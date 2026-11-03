"""Native Method contracts and ordered admission use one verified backend IR."""

from __future__ import annotations

import json
from pathlib import Path

import pytest
from test_scalar_generic_modules import _link
from test_source_system_execution import (
    _bundle,
    _cli,
    _compile,
    _install,
    _ok,
    _records,
    _run,
)

pytestmark = pytest.mark.system

COUNTER = """import pycircuit as ac
@ac.module
def Counter():
    x: ac.u8 = 10
    y: ac.u8 = 1
    stamp: ac.u8 = 0
    tick: ac.u8 = 0

    @ac.method
    def bump(delta: ac.u8) -> None:
        x = x + delta

    @ac.method(kind="query")
    def read() -> ac.u8:
        return x

    @ac.method(kind="query", private=True)
    def twice() -> ac.u8:
        first = read()
        second = read()
        return first + second

    @ac.method(kind="action")
    def record(value: ac.u8) -> None:
        stamp = value

    @ac.method
    def exercise(allow: ac.u1, check_cond: ac.u1, cond_pass: ac.u1) -> ac.u8:
        old = read()
        bump(3)
        bump(2)
        now = read()
        ac.guard(allow & (now == old + 5))
        y = y + 7
        bump(1)
        if check_cond:
            ac.guard(cond_pass)
        result = twice()
        record(result)
        return result

    @ac.rule
    def clock_tick() -> None:
        tick = tick + 1

    @ac.method(kind="query")
    def state() -> tuple[ac.u8, ac.u8, ac.u8, ac.u8]:
        return x, y, stamp, tick
"""

BENCH = """import pycircuit as ac
from checks.counter import Counter
@ac.system
def Exercise():
    counter = Counter()
    phase: ac.u3 = 0

    @ac.rule
    def next_phase() -> None:
        phase = phase + 1

    @ac.rule
    def observe() -> None:
        x, y, stamp, tick = counter.state()
        ac.log("info", "state", x, y, stamp, tick)

    @ac.rule
    def drive() -> None:
        allowed: ac.u1 = phase != 1
        check: ac.u1 = phase == 2
        result = counter.exercise(allowed, check, 0)
        ac.log("info", "success", result)
"""


def _known_verilator(generated, directory):
    receipt = json.loads((generated / "generated.json").read_text())
    rtl = [
        generated / item["path"] for item in receipt["files"] if item["role"] == "rtl"
    ]
    rtl.sort(key=lambda path: (path.name != "design_top.sv", str(path)))
    binary = directory / "known-verilator"
    command = [
        "verilator",
        "--binary",
        "--timing",
        "-CFLAGS",
        "-std=c++20",
        "--top-module",
        "pycircuit_sim",
        "--Mdir",
        str(directory / "verilated"),
        "-o",
        str(binary),
        "-j",
        "2",
        "-Wno-fatal",
        *map(str, sorted((_install() / "include/verilog").glob("*.v"))),
        *map(str, rtl),
        str(generated / "simulation_top.sv"),
    ]
    (directory / "verilator-command.json").write_text(json.dumps(command, indent=2))
    _ok(_run(command, timeout=180))
    return binary


def test_statement_guards_capture_candidates_and_discard_the_whole_caller(tmp_path):
    source = tmp_path / "source"
    source.mkdir()
    (source / "counter.py").write_text(COUNTER)
    (source / "bench.py").write_text(BENCH)
    provider, bench = tmp_path / "provider", tmp_path / "bench"
    _ok(_compile(source, "counter.py", provider))
    # Consumer compilation must use the published Method contract, not source.
    (source / "counter.py").rename(tmp_path / "counter-source-hidden.py")
    _ok(_compile(source, "bench.py", bench, [provider]))
    final = tmp_path / "system.ac"
    _ok(_link([provider, bench], "checks.bench.Exercise", final))
    original = final.read_bytes()
    expected_states = [
        (10, 1, 0, 0),
        (16, 8, 32, 1),
        (16, 8, 32, 2),
        (16, 8, 32, 3),
        (22, 15, 44, 4),
    ]
    expected_successes = [(0, 32), (1, 32), (6, 44), (7, 44), (8, 56), (9, 56)]
    traces = []
    for target in ("cpp", "verilog"):
        directory = tmp_path / (target + "-execution")
        directory.mkdir()
        binary = _bundle(final, directory, target)
        binaries = (
            [(binary, 1), (binary, 2)]
            if target == "cpp"
            else [(binary, 1), (_known_verilator(directory / target, directory), 1)]
        )
        for binary, workers in binaries:
            arguments = (
                ["--cycles", "5", "--workers", str(workers)]
                if target == "cpp"
                else ["+cycles=5"]
            )
            rows = _records(_ok(_run([str(binary), *arguments], timeout=30)))
            logs = [row for row in rows if row["kind"] == "log"]
            states = [row for row in logs if row["spec"]["event"] == "state"]
            success = [row for row in logs if row["spec"]["event"] == "success"]
            assert [
                tuple(int(value["value"]) for value in row["values"]) for row in states
            ] == [value for value in expected_states for _ in range(2)]
            assert [
                (int(row["evaluation_epoch"]), int(row["values"][0]["value"]))
                for row in success
            ] == expected_successes
            assert all(
                int(row["commit_epoch"]) == int(row["evaluation_epoch"]) + 1
                for row in logs
            )
            terminal = [row for row in rows if row["kind"] == "result"]
            assert len(terminal) == 1 and terminal[0]["status"] == "TERMINATED"
            traces.append([row for row in rows if row["kind"] != "result"])
    assert all(trace == traces[0] for trace in traces[1:])
    assert final.read_bytes() == original


@pytest.mark.parametrize(
    "body",
    [
        "        x = x + 1\n        return x\n",
        "        return bare_read()\n",
    ],
)
def test_query_contract_rejects_state_effects_and_unclassified_callees(tmp_path, body):
    source = tmp_path / "source"
    source.mkdir()
    (source / "counter.py").write_text(
        "import pycircuit as ac\n@ac.module\ndef Counter():\n"
        "    x: ac.u8 = 0\n    @ac.method\n"
        "    def bare_read() -> ac.u8:\n        return x\n"
        "    @ac.method(kind='query')\n    def read() -> ac.u8:\n" + body
    )
    unit = tmp_path / "unit"
    result = _compile(source, "counter.py", unit)
    assert result.returncode != 0, result.stdout + result.stderr
    assert "query" in result.stderr.lower(), result.stdout + result.stderr
    assert not unit.exists()


def test_retired_compose_is_not_silently_ignored(tmp_path):
    source = tmp_path / "source"
    source.mkdir()
    (source / "retired.py").write_text(
        "import pycircuit as ac\n@ac.module\ndef Owner():\n    value: ac.u8 = 0\n"
        "    @ac.method\n    def put() -> None:\n        value = 1\n"
        "    @ac.compose(target=value, operations=(put,))\n"
        "    def combine(old, ops):\n        return old\n"
    )
    unit = tmp_path / "unit"
    result = _compile(source, "retired.py", unit)
    assert result.returncode != 0, result.stdout + result.stderr
    assert not unit.exists()


def test_private_query_is_not_a_child_interface(tmp_path):
    source = tmp_path / "source"
    source.mkdir()
    (source / "counter.py").write_text(COUNTER)
    (source / "bench.py").write_text(
        "import pycircuit as ac\nfrom checks.counter import Counter\n"
        "@ac.system\ndef Exercise():\n    counter = Counter()\n"
        "    @ac.rule\n    def call() -> None:\n        value = counter.twice()\n"
    )
    provider = tmp_path / "provider"
    _ok(_compile(source, "counter.py", provider))
    consumer = tmp_path / "consumer"
    result = _compile(source, "bench.py", consumer, [provider])
    assert result.returncode != 0, result.stdout + result.stderr
    assert "private" in result.stderr.lower(), result.stdout + result.stderr
    assert not consumer.exists()


@pytest.mark.parametrize("separate_roots", [False, True])
def test_empty_action_retains_unique_invocation_contract(tmp_path, separate_roots):
    source = tmp_path / "source"
    source.mkdir()
    callers = (
        "    @ac.rule\n    def first() -> None:\n        notify(1)\n"
        "    @ac.rule\n    def second() -> None:\n        notify(2)\n"
        if separate_roots
        else "    @ac.rule(guard=lambda: False)\n    def first() -> None:\n"
        "        notify(1)\n        notify(2)\n"
    )
    (source / "counter.py").write_text(
        "import pycircuit as ac\n@ac.module\ndef Notice() -> None:\n"
        "    @ac.method(kind='action')\n    def notify(value: ac.u8) -> None:\n"
        "        pass\n" + callers
    )
    unit = tmp_path / "unit"
    _ok(_compile(source, "counter.py", unit))
    final = tmp_path / "final.ac"
    result = _link([unit], "checks.counter.Notice", final)
    assert result.returncode != 0, result.stdout + result.stderr
    assert "action" in result.stderr.lower(), result.stdout + result.stderr
    assert not final.exists()


def test_exclusive_calls_of_an_empty_action_do_not_require_a_fake_writer(tmp_path):
    source = tmp_path / "source"
    source.mkdir()
    (source / "counter.py").write_text(
        "import pycircuit as ac\n@ac.module\ndef Notice(flag: ac.u1) -> None:\n"
        "    @ac.method(kind='action')\n    def notify(value: ac.u8) -> None:\n"
        "        pass\n"
        "    @ac.rule\n    def first() -> None:\n"
        "        if flag:\n            notify(1)\n"
        "    @ac.rule\n    def second() -> None:\n"
        "        if not flag:\n            notify(2)\n"
    )
    unit = tmp_path / "unit"
    _ok(_compile(source, "counter.py", unit))
    final = tmp_path / "final.ac"
    _ok(_link([unit], "checks.counter.Notice", final))
    for target in ("cpp", "verilog"):
        _ok(_cli("emit", str(final), "--target", target, "-o", str(tmp_path / target)))


CELL = (
    Path(__file__).resolve().parents[2] / "examples/native_actions/notification.py"
).read_text()

CELL_BENCH = (
    (
        Path(__file__).resolve().parents[2]
        / "examples/native_actions/notification_system.py"
    )
    .read_text()
    .replace("from native_demo.notification", "from checks.cell")
)


def test_notification_actions_route_snapshots_without_binding_updater_roots(tmp_path):
    source = tmp_path / "source"
    source.mkdir()
    (source / "cell.py").write_text(CELL)
    (source / "bench.py").write_text(CELL_BENCH)
    provider, bench = tmp_path / "provider", tmp_path / "bench"
    _ok(_compile(source, "cell.py", provider))
    (source / "cell.py").rename(tmp_path / "cell-source-hidden.py")
    _ok(_compile(source, "bench.py", bench, [provider]))
    final = tmp_path / "system.ac"
    _ok(_link([provider, bench], "checks.bench.Exercise", final))
    original = final.read_bytes()
    expected = [
        (0, 0, 0, 0, 0, 0),
        (0, 10, 0, 20, 1, 1),
        (1, 21, 1, 11, 2, 2),
        (1, 21, 1, 11, 3, 3),
        (3, 23, 3, 13, 4, 4),
    ]
    traces = []
    for target in ("cpp", "verilog"):
        directory = tmp_path / (target + "-execution")
        directory.mkdir()
        binary = _bundle(final, directory, target)
        binaries = (
            [(binary, 1), (binary, 2)]
            if target == "cpp"
            else [(binary, 1), (_known_verilator(directory / target, directory), 1)]
        )
        for binary, workers in binaries:
            arguments = (
                ["--cycles", "5", "--workers", str(workers)]
                if target == "cpp"
                else ["+cycles=5"]
            )
            rows = _records(_ok(_run([str(binary), *arguments], timeout=30)))
            logs = [row for row in rows if row["kind"] == "log"]
            assert [
                tuple(int(value["value"]) for value in row["values"]) for row in logs
            ] == [value for value in expected for _ in range(2)]
            traces.append(logs)
    assert all(trace == traces[0] for trace in traces[1:])
    assert final.read_bytes() == original


def test_void_root_event_is_total_and_observes_late_admission(tmp_path):
    source = tmp_path / "source"
    source.mkdir()
    (source / "bench.py").write_text(
        "import pycircuit as ac\n@ac.system\ndef Exercise():\n"
        "    phase: ac.u8 = 0\n"
        "    @ac.rule\n    def next_phase() -> None:\n        phase = phase + 1\n"
        "    @ac.rule\n    def pulse() -> None:\n        ac.guard(phase != 2)\n"
        "    @ac.rule\n    def observe() -> None:\n"
        "        ac.log('info', 'pulse', ac.fired(pulse))\n"
    )
    unit, final = tmp_path / "unit", tmp_path / "system.ac"
    _ok(_compile(source, "bench.py", unit))
    _ok(_link([unit], "checks.bench.Exercise", final))
    for target in ("cpp", "verilog"):
        directory = tmp_path / target
        directory.mkdir()
        binary = _bundle(final, directory, target)
        if target == "verilog":
            binary = _known_verilator(directory / target, directory)
        arguments = ["--cycles", "5"] if target == "cpp" else ["+cycles=5"]
        rows = _records(_ok(_run([str(binary), *arguments], timeout=30)))
        logs = [row for row in rows if row["kind"] == "log"]
        assert [int(row["values"][0]["value"]) for row in logs] == [
            value for value in (1, 1, 0, 1, 1) for _ in range(2)
        ]


def _compile_pipe(tmp_path):
    repository = Path(__file__).resolve().parents[2]
    library = repository / "python/pycircuit/lib"
    pipe_unit = tmp_path / "pipe-unit"
    _ok(
        _cli(
            "compile",
            "-c",
            str(library / "pipe.py"),
            "--source-root",
            str(library),
            "--package-prefix",
            "pycircuit.lib",
            "-o",
            str(pipe_unit),
        )
    )
    return pipe_unit


@pytest.mark.parametrize("depth", [1, 3, 4])
def test_ordinary_pipe_library_preserves_elastic_concurrency(tmp_path, depth):
    repository = Path(__file__).resolve().parents[2]
    pipe_unit = _compile_pipe(tmp_path)
    source = tmp_path / "source"
    source.mkdir()
    (source / "pipeline.py").write_bytes(
        (repository / "examples/native_actions/pipeline.py").read_bytes()
    )
    stall_end = 8 if depth == 1 else 20
    cycles = 14 if depth == 1 else 30
    binding = "" if depth == 1 else f", Depth={depth}"
    (source / "bench.py").write_text(
        "import pycircuit as ac\nfrom checks.pipeline import Pipeline\n"
        "@ac.system\ndef Exercise():\n    phase: ac.u8 = 0\n"
        "    enabled = (phase != 2) & (phase != 8)\n"
        f"    draining = not ((phase >= 4) & (phase < {stall_end}))\n"
        f"    last, count = Pipeline(enabled, draining{binding})\n"
        "    @ac.rule\n    def next_phase() -> None:\n        phase = phase + 1\n"
        "    @ac.rule\n    def observe() -> None:\n"
        "        ac.log('info', 'output', last, count)\n"
    )
    pipeline_unit, bench_unit = tmp_path / "pipeline-unit", tmp_path / "bench-unit"
    _ok(_compile(source, "pipeline.py", pipeline_unit, [pipe_unit]))
    _ok(_compile(source, "bench.py", bench_unit, [pipe_unit, pipeline_unit]))
    final = tmp_path / "system.ac"
    _ok(_link([pipe_unit, pipeline_unit, bench_unit], "checks.bench.Exercise", final))
    # Independent FIFO equations: all stages read old tokens at the same edge.
    stages = [[], [], []]
    next_input, count, last = 0, 0, 0
    expected = []
    full_seen = False
    for phase in range(cycles):
        expected.append((last, count))
        full_seen |= all(len(stage) == depth for stage in stages)
        sink = bool(stages[2]) and not 4 <= phase < stall_end
        move3 = bool(stages[1]) and (len(stages[2]) < depth or sink)
        move2 = bool(stages[0]) and (len(stages[1]) < depth or move3)
        produce = phase not in (2, 8) and (len(stages[0]) < depth or move2)
        if sink:
            last, count = stages[2][0], count + 1
        incoming = [
            next_input + 1 if produce else None,
            stages[0][0] * 2 if move2 else None,
            stages[1][0] ^ 0x55 if move3 else None,
        ]
        for index, take in enumerate((move2, move3, sink)):
            if take:
                stages[index].pop(0)
            if incoming[index] is not None:
                stages[index].append(incoming[index])
        next_input += int(produce)
    assert full_seen
    for target in ("cpp", "verilog"):
        directory = tmp_path / target
        directory.mkdir()
        binary = _bundle(final, directory, target)
        if target == "verilog":
            binary = _known_verilator(directory / target, directory)
        arguments = (
            ["--cycles", str(cycles)] if target == "cpp" else [f"+cycles={cycles}"]
        )
        rows = _records(_ok(_run([str(binary), *arguments], timeout=30)))
        logs = [row for row in rows if row["kind"] == "log"]
        assert [
            tuple(int(value["value"]) for value in row["values"]) for row in logs
        ] == [value for value in expected for _ in range(2)]


def test_pipe_rejects_zero_depth_at_the_actual_instance(tmp_path):
    pipe_unit = _compile_pipe(tmp_path)
    source = tmp_path / "source"
    source.mkdir()
    (source / "bench.py").write_text(
        "import pycircuit as ac\nfrom pycircuit.lib.pipe import Pipe\n"
        "@ac.system\ndef Exercise():\n    pipe = Pipe(Depth=0)\n"
        "    @ac.rule\n    def drive() -> None:\n        pipe.push(1)\n"
    )
    bench, final = tmp_path / "bench-unit", tmp_path / "system.ac"
    result = _compile(source, "bench.py", bench, [pipe_unit])
    if result.returncode == 0:
        result = _link([pipe_unit, bench], "checks.bench.Exercise", final)
    assert result.returncode != 0, result.stdout + result.stderr
    assert not final.exists()


def test_pipe_nondefault_widths_keep_old_head_and_atomic_replacement(tmp_path):
    pipe_unit = _compile_pipe(tmp_path)
    source = tmp_path / "source"
    source.mkdir()
    (source / "bench.py").write_text(
        "import pycircuit as ac\nfrom pycircuit.lib.pipe import Pipe\n"
        "@ac.system\ndef Exercise():\n    small = Pipe(Width=5)\n    wide = Pipe(Width=13)\n"
        "    phase: ac.u13 = 0\n"
        "    @ac.rule\n    def next_phase() -> None:\n        phase = phase + 1\n"
        "    @ac.rule\n    def replace() -> None:\n"
        "        if phase != 0:\n            previous = small.pop()\n"
        "            other = wide.pop()\n"
        "            small.push(phase[:5] + 7)\n            wide.push(phase + 1000)\n"
        "            peek = small.peek()\n"
        "            assert peek == previous\n"
        "            ac.log('info', 'previous', previous, other)\n"
        "        else:\n            small.push(phase[:5] + 7)\n"
        "            wide.push(phase + 1000)\n"
        "        ac.guard(phase != 2)\n"
    )
    bench, final = tmp_path / "bench-unit", tmp_path / "system.ac"
    _ok(_compile(source, "bench.py", bench, [pipe_unit]))
    _ok(_link([pipe_unit, bench], "checks.bench.Exercise", final))
    expected = [
        (2, 7, 1000),
        (3, 7, 1000),
        (6, 8, 1001),
        (7, 8, 1001),
        (8, 10, 1003),
        (9, 10, 1003),
    ]
    for target in ("cpp", "verilog"):
        directory = tmp_path / target
        directory.mkdir()
        binary = _bundle(final, directory, target)
        if target == "verilog":
            binary = _known_verilator(directory / target, directory)
        args = ["--cycles", "5", "--workers", "2"] if target == "cpp" else ["+cycles=5"]
        logs = [
            row
            for row in _records(_ok(_run([str(binary), *args], timeout=30)))
            if row["kind"] == "log"
        ]
        assert [
            (
                int(row["evaluation_epoch"]),
                *(int(value["value"]) for value in row["values"]),
            )
            for row in logs
        ] == expected


FORWARD_BANK = """import pycircuit as ac
@ac.struct
class Pair:
    a: ac.u8
    b: ac.u8

@ac.module
def Bank(run: ac.u1, which: ac.u1, allow: ac.u1):
    pair: Pair = Pair(a=10, b=20)
    flag: ac.u1 = 0

    @ac.method
    def before() -> None:
        pair.b = 99

    @ac.method(kind="action")
    def apply(delta: ac.u8, select_a: ac.u1) -> None:
        if select_a:
            pair.a = pair.a + delta
        else:
            pair.b = pair.b + delta

    @ac.method
    def after() -> None:
        pair.a = pair.a + 7
        pair.b = 88

    @ac.rule
    def drive() -> None:
        if run:
            before()
            apply(3, which)
            after()
            flag = which
        ac.guard(allow)

    @ac.method(kind="query")
    def state() -> tuple[ac.u8, ac.u8, ac.u1, ac.u8, ac.u8, ac.u8, ac.u8, ac.u8]:
        marker: ac.u8 = 0
        if ac.forward(flag, source=drive):
            marker = 1
        return (pair.a, pair.b, apply.active,
                ac.forward(pair.a, source=apply), ac.forward(pair.b, source=apply),
                ac.forward(pair.a, source=drive), ac.forward(pair.b, source=drive), marker)
"""


def _forward_program(tmp_path, bank):
    source = tmp_path / "source"
    source.mkdir()
    (source / "bank.py").write_text(bank)
    (source / "bench.py").write_text(
        "import pycircuit as ac\nfrom checks.bank import Bank\n"
        "@ac.system\ndef Exercise():\n    phase: ac.u8 = 0\n"
        "    bank = Bank(phase < 4, (phase != 1) & (phase != 2), phase != 2)\n"
        "    @ac.rule\n    def next_phase() -> None:\n        phase = phase + 1\n"
        "    @ac.rule\n    def observe() -> None:\n"
        "        a, b, active, fa, fb, ra, rb, marker = bank.state()\n"
        "        ac.log('info', 'forward', a, b, active, fa, fb, ra, rb, marker)\n"
    )
    provider, bench = tmp_path / "provider", tmp_path / "bench"
    _ok(_compile(source, "bank.py", provider))
    (source / "bank.py").rename(tmp_path / "bank-source-hidden.py")
    _ok(_compile(source, "bench.py", bench, [provider]))
    final = tmp_path / "system.ac"
    return _link([provider, bench], "checks.bench.Exercise", final), final


def test_forward_rejects_overwritten_action_exit_without_a_history_certificate(
    tmp_path,
):
    result, final = _forward_program(tmp_path, FORWARD_BANK)
    assert result.returncode != 0
    assert "root-final" in result.stderr, result.stdout + result.stderr
    assert not final.exists()


def test_forward_uses_actual_leaf_writes_at_a_verified_final_boundary(tmp_path):
    source = FORWARD_BANK.replace(
        "        pair.a = pair.a + 7\n        pair.b = 88\n",
        "        flag = which\n",
    ).replace(
        "        if run:\n            before()\n            apply(3, which)\n"
        "            after()\n            flag = which\n        ac.guard(allow)\n",
        "        before()\n        apply(3, which)\n        after()\n"
        "        ac.guard(run & allow)\n",
    )
    result, final = _forward_program(tmp_path, source)
    _ok(result)
    expected = [
        (10, 20, 1, 13, 20, 13, 99, 1),
        (13, 99, 1, 13, 102, 13, 102, 0),
        (13, 102, 0, 13, 102, 13, 102, 0),
        (13, 102, 1, 16, 102, 16, 99, 1),
        (16, 99, 0, 16, 99, 16, 99, 1),
    ]
    for target in ("cpp", "verilog"):
        directory = tmp_path / target
        directory.mkdir()
        binary = _bundle(final, directory, target)
        binaries = (
            [(binary, 1), (binary, 2)]
            if target == "cpp"
            else [(_known_verilator(directory / target, directory), 1)]
        )
        for binary, workers in binaries:
            args = (
                ["--cycles", "5", "--workers", str(workers)]
                if target == "cpp"
                else ["+cycles=5"]
            )
            rows = _records(_ok(_run([str(binary), *args], timeout=30)))
            logs = [row for row in rows if row["kind"] == "log"]
            assert [
                tuple(int(value["value"]) for value in row["values"]) for row in logs
            ] == [value for value in expected for _ in range(2)]


@pytest.mark.parametrize("unknown", [False, True])
def test_scalar_forward_masks_are_observations_not_commit_domains(tmp_path, unknown):
    source = tmp_path / "source"
    source.mkdir()
    # Unknown chooses equal writes in both arms. Their joined native intent is
    # known one, although the OR of individual raw path masks remains unknown.
    body = (
        "        if select_a:\n            value = 5\n        else:\n            value = 5\n"
        if unknown
        else "        if select_a:\n            value = 7\n"
    )
    before = "" if unknown else "        value = 99\n"
    (source / "bank.py").write_text(
        "import pycircuit as ac\n@ac.module\ndef Bank():\n    value: ac.u8 = 0\n"
        "    @ac.method(kind='action')\n    def put(select_a: ac.u1) -> None:\n"
        + body
        + "    @ac.method\n    def drive(select_a: ac.u1) -> None:\n"
        + before
        + "        put(select_a)\n"
        "    @ac.method(kind='query')\n    def state() -> tuple[ac.u8, ac.u8]:\n"
        "        return value, ac.forward(value, source=put)\n"
    )
    choose = "ac.four_state('x')" if unknown else "phase[:1]"
    checks = (
        "        if phase == 0:\n"
        "            assert ac.case_eq(view, ac.four_state('00000x0x'))\n"
        "        else:\n            assert stored == 5\n            assert view == 5\n"
        if unknown
        else "        ac.log('info', 'view', view)\n"
    )
    (source / "bench.py").write_text(
        "import pycircuit as ac\nfrom checks.bank import Bank\n"
        "@ac.system\ndef Exercise():\n    phase: ac.u8 = 0\n    bank = Bank()\n"
        "    @ac.rule\n    def next_phase() -> None:\n        phase = phase + 1\n"
        "    @ac.rule\n    def drive() -> None:\n        bank.drive(" + choose + ")\n"
        "    @ac.rule\n    def observe() -> None:\n        stored, view = bank.state()\n"
        "        ac.log('info', 'stored', stored)\n" + checks
    )
    provider, bench, final = (
        tmp_path / "provider",
        tmp_path / "bench",
        tmp_path / "system.ac",
    )
    _ok(_compile(source, "bank.py", provider))
    _ok(_compile(source, "bench.py", bench, [provider]))
    _ok(_link([provider, bench], "checks.bench.Exercise", final))
    expected_stored = [0, 5, 5, 5] if unknown else [0, 99, 7, 99]
    expected_view = [] if unknown else [0, 7, 7, 7]
    for target in ("cpp", "verilog"):
        directory = tmp_path / target
        directory.mkdir()
        binary = _bundle(final, directory, target)
        if target == "verilog" and not unknown:
            binary = _known_verilator(directory / target, directory)
        arguments = (
            ["--cycles", "4", "--workers", "2"] if target == "cpp" else ["+cycles=4"]
        )
        rows = _records(_ok(_run([str(binary), *arguments], timeout=30)))
        for event, expected in (("stored", expected_stored), ("view", expected_view)):
            assert [
                int(row["values"][0]["value"])
                for row in rows
                if row["kind"] == "log" and row["spec"]["event"] == event
            ] == [value for value in expected for _ in range(2)]
