"""Readable export preserves arithmetic sharing, widths and physical controls."""

import json
import re
from pathlib import Path

import pytest
from test_source_system_execution import ROOT, _cli, _ok, _run

pytestmark = pytest.mark.system
SOURCE = """import pycircuit as ac
@ac.module
def Counter(enable: ac.u1) -> ac.u8:
    count: ac.u8 = 0
    @ac.rule
    def increment() -> None:
        if enable:
            count = count + 1
    return count
@ac.module
def Fanout(value: ac.u8) -> tuple[ac.u8, ac.u8]:
    @ac.rule
    def compute() -> tuple[ac.u8, ac.u8]:
        shared = value + 1
        return shared, shared
    first, second = compute
    return first, second
@ac.module
def Narrow(first: ac.u4, second: ac.u4) -> ac.u8:
    @ac.rule
    def compute() -> ac.u8:
        narrow: ac.u4 = first + second
        return ac.concat(narrow, narrow)
    return compute
@ac.module
def Widened(first: ac.u4, second: ac.u4) -> ac.u8:
    @ac.rule
    def compute() -> ac.u8:
        narrow: ac.u4 = first + second
        wide: ac.u8 = narrow
        return wide
    return compute
@ac.module
def Slice(value: ac.u8) -> ac.u4:
    @ac.rule
    def compute() -> ac.u4:
        added = value + 1
        return added[:4]
    return compute
@ac.module
def Collisions(clk: ac.u1, rst: ac.u1, enable: ac.u1) -> ac.u8:
    result: ac.u8 = 5
    @ac.rule
    def update() -> None:
        if enable:
            a: ac.u8 = clk
            b: ac.u8 = rst
            result = result + a + b
    return result
@ac.module
def BitForms(value: ac.u1) -> tuple[ac.u1, ac.u1, ac.u1, ac.u1]:
    @ac.rule
    def compute() -> tuple[ac.u1, ac.u1, ac.u1, ac.u1]:
        return value & 1, value & 0, value | 1, value ^ value
    return compute
@ac.module
def ac_readable_presentation_Counter(value: ac.u8) -> ac.u8:
    return value
@ac.module
def dffe(value: ac.u8) -> ac.u8:
    return value
@ac.module
def ShortNamesConflict(enable: ac.u1, value: ac.u8) -> tuple[ac.u8, ac.u8, ac.u8]:
    first = Counter(enable)
    second = ac_readable_presentation_Counter(value)
    third = dffe(value + 1)
    return first, second, third
"""


@pytest.fixture(scope="module")
def readable_designs(tmp_path_factory):
    root = tmp_path_factory.mktemp("readable-physical")
    source = root / "presentation.py"
    source.write_text(SOURCE)
    unit = root / "unit"
    _ok(
        _cli(
            "compile",
            "-c",
            str(source),
            "--source-root",
            str(root),
            "--package-prefix",
            "readable",
            "-o",
            str(unit),
        )
    )
    result = {}
    for name in (
        "Counter",
        "Fanout",
        "Narrow",
        "Widened",
        "Slice",
        "Collisions",
        "BitForms",
        "ShortNamesConflict",
    ):
        final = root / (name + ".ac")
        _ok(
            _cli(
                "link",
                str(unit),
                "--top",
                "readable.presentation." + name,
                "-o",
                str(final),
            )
        )
        output = root / name
        _ok(
            _cli(
                "emit",
                str(final),
                "--target",
                "verilog",
                "--rtl-mode",
                "physical",
                "-o",
                str(output),
            )
        )
        result[name] = output
    return result


def design_text(output):
    text = "\n".join(path.read_text() for path in (output / "sources").rglob("*.v"))
    module = re.search(
        r"(?ms)^module (?:ac_readable_presentation_)?"
        + re.escape(output.name)
        + r"\b.*?^endmodule\b",
        text,
    )
    assert module, output.name
    return module.group()


def simulate(output, tmp_path, body, *, verilator=False):
    manifest = json.loads((output / "generated.json").read_text())
    ports = json.loads((output / "ports.json").read_text())
    declarations, connections = [], []
    for row in ports["inputs"]:
        name = (
            "clk"
            if row["ordinal"] == ports["domains"]["clock"]
            else "rst" if row["ordinal"] == ports["domains"]["reset"] else row["name"]
        )
        declarations.append(f"logic [{row['width'] - 1}:0] {name} = '0;")
        connections.append(f".{row['wire']}({name})")
    for index, row in enumerate(ports["outputs"]):
        declarations.append(f"wire [{row['width'] - 1}:0] result_{index};")
        connections.append(f".{row['wire']}(result_{index})")
    tb = tmp_path / "test.sv"
    tb.write_text(
        "module tb;\n"
        + "\n".join(declarations)
        + "\n"
        + manifest["root_rtl_name"]
        + " dut("
        + ",".join(connections)
        + ");\n"
        + "task step;#2;clk=1;#2;clk=0;#2;endtask\n"
        + "initial begin\n"
        + body
        + '\n$display("READABILITY_COMPLETE");$finish;end\nendmodule\n'
    )
    sources = [
        str(output / row["path"])
        for row in manifest["files"]
        if Path(row["path"]).suffix in (".v", ".sv")
    ]
    sources += [
        str(ROOT / "include/verilog/dff.v"),
        str(ROOT / "include/verilog/dffe.v"),
        str(tb),
    ]
    binary = tmp_path / ("test_sim" if verilator else "test.vvp")
    if verilator:
        _ok(
            _run(
                [
                    "verilator",
                    "--binary",
                    "--timing",
                    "-Wno-fatal",
                    "--top-module",
                    "tb",
                    "--Mdir",
                    str(tmp_path / "obj"),
                    "-o",
                    str(binary),
                    "-j",
                    "2",
                    *sources,
                ],
                timeout=240,
            )
        )
        transcript = _ok(_run([str(binary)]))
    else:
        _ok(_run(["iverilog", "-g2012", "-s", "tb", "-o", str(binary), *sources]))
        transcript = _ok(_run(["vvp", str(binary)]))
    assert "READABILITY_COMPLETE" in transcript
    return transcript


@pytest.mark.parametrize("verilator", [False, True])
def test_counter_hold_wrap_reset_and_startup(readable_designs, tmp_path, verilator):
    body = """
#1;if(result_0!==0)$fatal(1,"declared startup");
enable=1;
for(integer i=1;i<=260;i=i+1)begin
    step();if(result_0!==(i%256))$fatal(1,"increment/wrap");
end
enable=0;step();if(result_0!==4)$fatal(1,"hold");
rst=1;#1;if(result_0!==4)$fatal(1,"asynchronous reset");
step();if(result_0!==0)$fatal(1,"synchronous reset");
rst=0;enable=1;step();if(result_0!==1)$fatal(1,"resume");
"""
    transcript = simulate(
        readable_designs["Counter"], tmp_path, body, verilator=verilator
    )
    assert "PYCIRCUIT_PHYSICAL_FAULT" not in transcript
    text = design_text(readable_designs["Counter"])
    assert "always_ff" in text and "logic [7:0] count;" in text
    assert "else if (enable)" in text
    assert "pyc_write_" not in text and "pyc_commit_count" not in text
    assert "posedge clk" in text
    assert "pyc_net_" not in text


@pytest.mark.parametrize(
    "fault",
    [
        "enable=1'bx;step();",
        "enable=1'bz;step();",
        "rst=1'bx;step();",
        "rst=1'bz;step();",
        "#2;clk=1'bx;#2;",
        "#2;clk=1'bz;#2;",
    ],
)
def test_counter_unknown_controls_keep_sticky_zero_commit(
    readable_designs, tmp_path, fault
):
    body = (
        "enable=1;step();\n"
        + fault
        + "\n"
        + """
if(result_0!==1)$fatal(1,"fault changed state");
clk=0;rst=0;enable=1;step();
if(result_0!==1)$fatal(1,"fault was not sticky");
rst=1;step();if(result_0!==1)$fatal(1,"reset recovered failure");
"""
    )
    transcript = simulate(readable_designs["Counter"], tmp_path, body)
    assert transcript.count("PYCIRCUIT_PHYSICAL_FAULT") == 1


@pytest.mark.parametrize("design", ["Fanout", "Narrow"])
def test_shared_arithmetic_is_not_duplicated_or_widened(
    readable_designs, tmp_path, design
):
    output = readable_designs[design]
    assert len(re.findall(r"\s\+\s", design_text(output))) == 1
    body = (
        'value=255;#2;if(result_0!==0 || result_1!==0)$fatal(1,"wrap");'
        'value=37;#2;if(result_0!==38 || result_1!==38)$fatal(1,"fanout");'
        if design == "Fanout"
        else 'first=15;second=2;#2;if(result_0!==8\'h11)$fatal(1,"narrow wrap");'
        'first=7;second=6;#2;if(result_0!==8\'hdd)$fatal(1,"concat order");'
    )
    assert "PYCIRCUIT_PHYSICAL_FAULT" not in simulate(output, tmp_path, body)


def test_inlined_add_truncates_before_widening(readable_designs, tmp_path):
    body = """
for(integer a=0;a<16;a=a+1)begin
    for(integer b=0;b<16;b=b+1)begin
        first=a;second=b;#2;
        if(result_0!==((a+b)%16))$fatal(1,"widening changed narrow addition");
    end
end
"""
    assert "PYCIRCUIT_PHYSICAL_FAULT" not in simulate(
        readable_designs["Widened"], tmp_path, body
    )


def test_partial_slice_keeps_a_legal_width_boundary(readable_designs, tmp_path):
    body = """
for(integer a=0;a<256;a=a+1)begin
    value=a;#2;
    if(result_0!==((a+1)%16))$fatal(1,"partial slice width/order");
end
"""
    assert "PYCIRCUIT_PHYSICAL_FAULT" not in simulate(
        readable_designs["Slice"], tmp_path, body
    )


def test_source_ports_and_state_export_collisions(readable_designs, tmp_path):
    output = readable_designs["Collisions"]
    ports = json.loads((output / "ports.json").read_text())
    wire_by_name = {row["name"]: row["wire"] for row in ports["inputs"]}
    assert wire_by_name["clk"] == "clk" and wire_by_name["rst"] == "rst"
    assert wire_by_name["pyc_clk"] == "clk_1"
    assert wire_by_name["pyc_rst"] == "rst_1"
    assert "logic [7:0] result_1;" in design_text(output)
    # The standard simulation adapter deliberately aliases domain pins to clk/rst.
    # Drive authored data ports through an independent adapter for this test.
    manifest = json.loads((output / "generated.json").read_text())
    tb = tmp_path / "collision.sv"
    tb.write_text(
        "module tb;logic clock=0,reset=0,a=0,b=0,en=0;wire[7:0]q;\n"
        + manifest["root_rtl_name"]
        + " dut(.clk(a),.rst(b),.enable(en),"
        ".clk_1(clock),.rst_1(reset),.result(q));\n"
        + """
task step;#2;clock=1;#2;clock=0;#2;endtask
initial begin
    #1;if(q!==5)$fatal(1,"startup");
    en=1;a=1;b=0;step();if(q!==6)$fatal(1,"clock data collision");
    a=0;b=1;step();if(q!==7)$fatal(1,"reset data collision");
    reset=1;step();if(q!==5)$fatal(1,"physical reset collision");
    $finish;
end
endmodule
"""
    )
    files = [
        str(output / row["path"])
        for row in manifest["files"]
        if Path(row["path"]).suffix in (".v", ".sv")
    ]
    binary = tmp_path / "collision.vvp"
    _ok(_run(["iverilog", "-g2012", "-s", "tb", "-o", str(binary), *files, str(tb)]))
    assert "PYCIRCUIT_PHYSICAL_FAULT" not in _ok(_run(["vvp", str(binary)]))


def test_boolean_rendering_preserves_x_and_z_payloads(readable_designs, tmp_path):
    body = """
value=0;#2;if(result_0!==0 || result_1!==0 || result_2!==1 || result_3!==0)$fatal(1,"zero");
value=1;#2;if(result_0!==1 || result_1!==0 || result_2!==1 || result_3!==0)$fatal(1,"one");
value=1'bx;#2;if(result_0!==1'bx || result_1!==0 || result_2!==1 || result_3!==1'bx)$fatal(1,"X payload");
value=1'bz;#2;if(result_0!==1'bx || result_1!==0 || result_2!==1 || result_3!==1'bx)$fatal(1,"Z normalization");
"""
    assert "PYCIRCUIT_PHYSICAL_FAULT" not in simulate(
        readable_designs["BitForms"], tmp_path, body
    )


def test_original_module_names_do_not_collide_with_fallbacks_or_primitives(
    readable_designs, tmp_path
):
    body = 'value=37;enable=1;step();if(result_0!==1 || result_1!==37 || result_2!==38)$fatal(1,"module identity collision");'
    assert "PYCIRCUIT_PHYSICAL_FAULT" not in simulate(
        readable_designs["ShortNamesConflict"], tmp_path, body
    )


def test_managed_domain_ports_keep_the_existing_public_abi(readable_designs, tmp_path):
    final = readable_designs["Counter"].parent / "Counter.ac"
    output = tmp_path / "managed"
    _ok(
        _cli(
            "emit",
            str(final),
            "--target",
            "verilog",
            "--rtl-mode",
            "managed",
            "-o",
            str(output),
        )
    )
    text = (output / "design_top.sv").read_text()
    ports = json.loads((output / "ports.json").read_text())
    wires = {row["name"]: row["wire"] for row in ports["inputs"]}
    for original, encoded in (
        ("pyc_clk", "pyc_7079635f636c6b"),
        ("pyc_rst", "pyc_7079635f727374"),
    ):
        assert wires[original] == encoded
        assert re.search(r"\b" + encoded + r"\b", text)
