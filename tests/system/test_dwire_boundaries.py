"""DWire hierarchy, reset and reached-control boundaries through public tools."""

from __future__ import annotations

import json
import shutil

import pytest
from test_ordered_rules import _check_final
from test_source_system_execution import _bundle, _cli, _compile, _ok, _records, _run

pytestmark = pytest.mark.system


def test_cross_module_writes_survive_header_import_and_anchor_reload(tmp_path):
    source = tmp_path / "source"
    source.mkdir()
    provider_source = source / "counter.py"
    provider_source.write_text(
        """import pycircuit as ac
@ac.module
def Counter():
    event: ac.u8 = ac.dwire()
    total: ac.u8 = 0
    @ac.method
    def send(value: ac.u8, enable: ac.u1) -> None:
        if enable:
            event = value
    @ac.method
    def read() -> ac.u8:
        return total
    @ac.rule
    def accumulate() -> None:
        total = total + event
"""
    )
    (source / "bench.py").write_text(
        """import pycircuit as ac
from checks.counter import Counter
@ac.system
def Exercise():
    left = Counter()
    right = Counter()
    phase: ac.u2 = 0
    @ac.rule
    def produce_left() -> None:
        left.send(7, phase == 0)
    @ac.rule
    def produce_right() -> None:
        right.send(4, phase == 1)
    @ac.rule
    def advance() -> None:
        phase = phase + 1
    @ac.rule
    def observe() -> None:
        ac.log("info", "wire instances", left.read() + right.read())
"""
    )
    provider, consumer = tmp_path / "provider", tmp_path / "consumer"
    _ok(_compile(source, "counter.py", provider))
    receipt = json.loads((provider / "unit.json").read_text())
    body = provider / receipt["files"]["body"]
    hidden = tmp_path / "hidden-provider.ac"
    provider_source.unlink()
    body.rename(hidden)
    try:
        _ok(_compile(source, "bench.py", consumer, [provider]))
    finally:
        hidden.rename(body)
    anchor = tmp_path / "anchor"
    _ok(
        _cli(
            "link",
            str(provider),
            str(consumer),
            "--top",
            "checks.bench.Exercise",
            "--target",
            "anchor",
            "-o",
            str(anchor),
        )
    )
    for directory in (source, provider, consumer):
        shutil.rmtree(directory)
    final = tmp_path / "reloaded.ac"
    _ok(
        _cli(
            "link", "--from-anchor", str(anchor), "--target", "final", "-o", str(final)
        )
    )
    _check_final(final, tmp_path, [0, 7, 11, 11])


def _finite_program(tmp_path, samples, body):
    source = tmp_path / "source"
    source.mkdir()
    (source / "scenario.py").write_text(
        f"""import pycircuit as ac
@ac.module
def Circuit() -> ac.u8:
    count: ac.u8 = 3
{body}
@ac.system(samples={samples})
def Exercise():
    value = Circuit()
    @ac.rule
    def observe() -> None:
        ac.log("info", "wire boundary", value)
"""
    )
    unit = tmp_path / "unit"
    _ok(_compile(source, "scenario.py", unit))
    final = tmp_path / "scenario.ac"
    _ok(_cli("link", str(unit), "--top", "checks.scenario.Exercise", "-o", str(final)))
    return final


def test_reset_changes_registers_without_adding_wire_history(tmp_path):
    final = _finite_program(
        tmp_path,
        "((0, 0), (1, 0), (0, 1), (1, 1), (0, 0), (1, 0), (0, 0))",
        """    data: ac.u8 = ac.dwire()
    @ac.rule
    def produce() -> None:
        data = 4
    @ac.rule
    def consume() -> None:
        count = count + data
    return count + data
""",
    )
    transcripts = []
    for target in ("cpp", "verilog"):
        destination = tmp_path / target
        destination.mkdir()
        runner = _bundle(final, destination, target)
        for workers in (1, 2) if target == "cpp" else (1,):
            arguments = ["--workers", str(workers)] if target == "cpp" else []
            rows = _records(_ok(_run([str(runner), *arguments])))
            logs = [row for row in rows if row["kind"] == "log"]
            assert [int(row["values"][0]["value"]) for row in logs] == [
                7,
                7,
                11,
                11,
                7,
                7,
                11,
            ]
            transcripts.append([row for row in rows if row["kind"] != "result"])
    assert transcripts[0] == transcripts[1] == transcripts[2]


def test_unknown_wire_control_fails_before_the_rising_epoch_is_published(tmp_path):
    final = _finite_program(
        tmp_path,
        "((0, 0), (1, 0))",
        """    event: ac.u1 = ac.dwire()
    @ac.rule
    def produce() -> None:
        event = ac.four_state("x")
    @ac.rule(guard=lambda: event)
    def consume() -> None:
        count = count + 1
    return count
""",
    )
    for target in ("cpp", "verilog"):
        destination = tmp_path / target
        destination.mkdir()
        runner = _bundle(final, destination, target)
        for workers in (1, 2) if target == "cpp" else (1,):
            arguments = ["--workers", str(workers)] if target == "cpp" else []
            result = _run([str(runner), *arguments])
            assert result.returncode != 0
            # Reached guards are checked at a rising edge outside reset.
            # The prior low sample may publish, but the failing high sample may not.
            logs = [row for row in _records(result.stdout) if row["kind"] == "log"]
            assert [int(row["values"][0]["value"]) for row in logs] == [3]
