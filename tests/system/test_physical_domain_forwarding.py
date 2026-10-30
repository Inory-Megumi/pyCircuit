"""Transparent child domain outputs remain clocks through all actual uses."""

import os
import re

import pytest
from test_physical_projection_rejections import (
    _block_arguments,
    _module_span,
    _ordinary_verified,
    _physical_rejected,
    _split_top,
)
from test_source_system_execution import _cli, _compile, _ok, _run

pytestmark = pytest.mark.system
SOURCE = """import pycircuit as ac
@ac.module
def Cell():
    saved: ac.u8 = 7
    @ac.method
    def write(incoming: ac.u8) -> None:
        saved = incoming
    @ac.method
    def read() -> ac.u8:
        return saved
@ac.module
def Parent(incoming: ac.u8, enable: ac.u1) -> ac.u8:
    cell = Cell()
    @ac.rule
    def update() -> None:
        if enable:
            cell.write(incoming)
    @ac.rule
    def observe() -> ac.u8:
        return cell.read()
    return observe
"""


def source_final(tmp_path, *, bit=False):
    source = tmp_path / "source"
    source.mkdir()
    text = SOURCE
    if bit:
        text = text.replace("enable: ac.u1) -> ac.u8", "enable: ac.u1) -> ac.u1")
        text = text.replace("def observe() -> ac.u8", "def observe() -> ac.u1")
        text = text.replace("return cell.read()", "return cell.read()[:1]")
    (source / "design.py").write_text(text)
    unit = tmp_path / "unit"
    _ok(_compile(source, "design.py", unit))
    final = tmp_path / "parent.ac"
    _ok(_cli("link", str(unit), "--top", "checks.design.Parent", "-o", str(final)))
    return final


def child_clock(lines):
    start, end = _module_span(lines, "checks.design.Parent")
    index = next(
        i
        for i in range(start, end)
        if '"ac.instance"' in lines[i] and "@checks.design.Cell" in lines[i]
    )
    group = re.match(r"\s*(%\w+):(\d+) =", lines[index])
    assert group and int(group[2]) >= 3
    types = lines[index].rsplit(" -> (", 1)[1].split(") loc(", 1)[0]
    clock_type = _split_top(types)[0]
    return start, end, index, group[1] + "#0", clock_type


def test_method_clock_forwarding_emits_physical(tmp_path):
    final = source_final(tmp_path)
    _ok(
        _cli(
            "emit",
            str(final),
            "--target",
            "verilog",
            "--rtl-mode",
            "physical",
            "-o",
            str(tmp_path / "physical"),
        )
    )
    text = "\n".join(
        path.read_text() for path in (tmp_path / "physical" / "sources").rglob("*.v")
    )
    assert "clk_capture" not in text and "rst_capture" not in text


def test_child_forwarded_clock_cannot_be_dead_arithmetic_data(tmp_path):
    final = source_final(tmp_path)
    lines = final.read_text().splitlines()
    _, _, index, clock, clock_type = child_clock(lines)
    lines.insert(
        index + 1,
        f'    %clock_data = "ac.bits.binary"({clock}, {clock}) '
        f'{{opcode = "xor"}} : ({clock_type}, {clock_type}) -> {clock_type}',
    )
    final.write_text("\n".join(lines) + "\n")
    _ordinary_verified(final)
    _physical_rejected(final, tmp_path, "forbids clock use as data")


def test_child_forwarded_clock_cannot_be_root_payload(tmp_path):
    final = source_final(tmp_path, bit=True)
    lines = final.read_text().splitlines()
    start, end, _, clock, clock_type = child_clock(lines)
    output = next(
        i for i in range(start, end) if lines[i].startswith('    "ac.yield"(')
    )
    types = lines[output].rsplit(": (", 1)[1].rsplit(") -> ()", 1)[0]
    payload_type = _split_top(types)[0]
    begin = lines[output].index("(") + 1
    comma = lines[output].find(",", begin)
    close = lines[output].index(")", begin)
    finish = min(comma, close) if comma >= 0 else close
    lines[output] = lines[output][:begin] + "%clock_payload" + lines[output][finish:]
    low = '#ac.static_expr<{kind = "literal", location = {path = "design.py", line = 1 : i64, column = 1 : i64, end_line = 1 : i64, end_column = 2 : i64}, origin = {site = {definition = @checks.design.Parent, ast_path = []}, expansion = []}, value = {kind = "integer", value = #ac.math_int<0>}}>'
    lines.insert(
        output,
        f'    %clock_payload = "ac.bits.extract"({clock}) '
        f"{{low = {low}}} : ({clock_type}) -> {payload_type}",
    )
    final.write_text("\n".join(lines) + "\n")
    _ordinary_verified(final)
    _physical_rejected(final, tmp_path, "forbids clock use as data")


def test_child_storage_cannot_substitute_reset_for_clock(tmp_path):
    final = source_final(tmp_path)
    lines = final.read_text().splitlines()
    start, end = _module_span(lines, "checks.design.Cell")
    block = next(i for i in range(start, end) if lines[i].lstrip().startswith("^bb0"))
    arguments = _block_arguments(lines[block])
    clock, reset = arguments[0][0], arguments[1][0]
    storage = next(
        i
        for i in range(start, end)
        if '"ac.instance"' in lines[i] and "@pycircuit.__builtins__.dffe" in lines[i]
    )
    assert '"ac.instance"(' + clock + "," in lines[storage]
    lines[storage] = lines[storage].replace(
        '"ac.instance"(' + clock + ",", '"ac.instance"(' + reset + ",", 1
    )
    final.write_text("\n".join(lines) + "\n")
    result = _run(
        [os.environ["PYCIRCUIT_LINKER"], "--design", str(final), "--verify-only"]
    )
    assert result.returncode != 0
    assert (
        "sampled domain differs from target storage physical pins"
        in result.stdout + result.stderr
    )
