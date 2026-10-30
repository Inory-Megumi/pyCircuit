"""Reset-based hardware export is separate from instrumented physical RTL."""

import json
import re

import pytest
from test_physical_rtl_readability import readable_designs as _readable_designs
from test_physical_rtl_readability import simulate
from test_source_system_execution import _cli, _ok

pytestmark = pytest.mark.system
readable_designs = _readable_designs


def emit_synthesis(readable_designs, tmp_path, design):
    final = readable_designs[design].parent / (design + ".ac")
    output = tmp_path / design
    _ok(
        _cli(
            "emit",
            str(final),
            "--target",
            "verilog",
            "--rtl-mode",
            "synthesis",
            "-o",
            str(output),
        )
    )
    manifest = json.loads((output / "generated.json").read_text())
    assert manifest["rtl_mode"] == "synthesis"
    text = "\n".join(
        (output / row["path"]).read_text()
        for row in manifest["files"]
        if row["path"].endswith((".v", ".sv"))
    )
    assert not re.search(
        r"\binitial\b|__checks|\$isunknown|\$display|\$fatal|pyc_phase", text
    )
    assert "pyc_root_commit_ok" not in text and "pyc_physical_fault" not in text
    assert "include/verilog/dff" not in (output / "CMakeLists.txt").read_text()
    ports = json.loads((output / "ports.json").read_text())
    assert not any(row["role"] == "commit_permission" for row in ports["controls"])
    return output


@pytest.mark.parametrize("verilator", [False, True])
def test_synthesis_counter_reset_hold_wrap(readable_designs, tmp_path, verilator):
    output = emit_synthesis(readable_designs, tmp_path, "Counter")
    body = """
rst=1;step();if(result_0!==0)$fatal(1,"reset");
rst=0;enable=1;
for(integer i=1;i<=260;i=i+1)begin
    step();if(result_0!==(i%256))$fatal(1,"increment/wrap");
end
enable=0;step();if(result_0!==4)$fatal(1,"hold");
rst=1;#1;if(result_0!==4)$fatal(1,"reset must be synchronous");
step();if(result_0!==0)$fatal(1,"reset must beat enable");
"""
    simulate(output, tmp_path, body, verilator=verilator)


def test_synthesis_has_no_implicit_startup_value(readable_designs, tmp_path):
    output = emit_synthesis(readable_designs, tmp_path, "Counter")
    body = """
#1;if(!$isunknown(result_0))$fatal(1,"unexpected startup initialization");
enable=0;step();if(!$isunknown(result_0))$fatal(1,"hold before reset");
rst=1;#1;if(!$isunknown(result_0))$fatal(1,"asynchronous initialization");
step();if(result_0!==0)$fatal(1,"reset value");
"""
    simulate(output, tmp_path, body)


@pytest.mark.parametrize("design", ["Fanout", "Narrow"])
def test_synthesis_keeps_shared_arithmetic_and_widths(
    readable_designs, tmp_path, design
):
    output = emit_synthesis(readable_designs, tmp_path, design)
    text = "\n".join(path.read_text() for path in (output / "sources").rglob("*.v"))
    module = re.search(r"(?ms)^module " + design + r"\b.*?^endmodule\b", text).group()
    assert len(re.findall(r"\s\+\s", module)) == 1
    body = (
        'value=255;#2;if(result_0!==0 || result_1!==0)$fatal(1,"wrap");'
        'value=37;#2;if(result_0!==38 || result_1!==38)$fatal(1,"fanout");'
        if design == "Fanout"
        else 'first=15;second=2;#2;if(result_0!==8\'h11)$fatal(1,"narrow wrap");'
    )
    simulate(output, tmp_path, body)


def test_synthesis_requires_verilog_target(readable_designs, tmp_path):
    final = readable_designs["Counter"].parent / "Counter.ac"
    result = _cli(
        "emit",
        str(final),
        "--target",
        "cpp",
        "--rtl-mode",
        "synthesis",
        "-o",
        str(tmp_path / "bad"),
    )
    assert result.returncode != 0
    assert "requires the verilog target" in result.stdout + result.stderr
    assert not (tmp_path / "bad").exists()


def test_synthesis_preserves_nominal_storage_and_declared_reset(tmp_path):
    source = tmp_path / "record.py"
    source.write_text(
        """import pycircuit as ac
@ac.struct
class Payload:
    data: ac.u8
@ac.module
def RecordState(incoming: ac.u8) -> ac.u8:
    saved: Payload = Payload(data=7)
    @ac.rule
    def update() -> None:
        saved = Payload(data=incoming)
    return saved.data
"""
    )
    unit = tmp_path / "unit"
    _ok(
        _cli(
            "compile",
            "-c",
            str(source),
            "--source-root",
            str(tmp_path),
            "--package-prefix",
            "synthesis_checks",
            "-o",
            str(unit),
        )
    )
    final = tmp_path / "record.ac"
    _ok(
        _cli(
            "link",
            str(unit),
            "--top",
            "synthesis_checks.record.RecordState",
            "-o",
            str(final),
        )
    )
    output = tmp_path / "supported"
    _ok(
        _cli(
            "emit",
            str(final),
            "--target",
            "verilog",
            "--rtl-mode",
            "synthesis",
            "-o",
            str(output),
        )
    )
    text = "\n".join(path.read_text() for path in (output / "sources").rglob("*.v"))
    assert "Payload_t saved;" in text
    assert "always_ff @(posedge clk)" in text
    assert "saved <=" in text and "8'd7" in text
    assert not re.search(r"\binitial\b|__checks|pyc_phase", text)
