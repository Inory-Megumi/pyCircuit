"""Presentation decisions follow the typed graph, not spelling or search depth."""

import json
import os
import re
from collections import Counter

import pytest
from test_physical_rtl_readability import simulate
from test_scalar_generic_modules import _link
from test_source_system_execution import _cli, _compile, _ok, _run

pytestmark = pytest.mark.system


def _hardware(tmp_path, text):
    source = tmp_path / "source"
    source.mkdir()
    (source / "probe.py").write_text(text)
    unit, final, output = tmp_path / "unit", tmp_path / "final.ac", tmp_path / "rtl"
    _ok(_compile(source, "probe.py", unit))
    _ok(_link([unit], "checks.probe.Probe", final))
    original = final.read_bytes()
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
    assert final.read_bytes() == original
    mapping = json.loads((output / "rtl-names.json").read_text())
    plans = [module["presentation_plan"] for module in mapping["modules"]]
    assert plans and all(plan["complete"] for plan in plans)
    for plan in plans:
        assert plan["live_values"] == plan["covered_values"]
        assert not plan["unexpected_emitted_values"]
        for node in plan["values"]:
            assert node["context"] and node["original_value"] >= 0
            if node["uses"] > 1:
                assert node["materialization"] != "single-use bounded expression"
            if node["arity"] <= 3:
                assert node["rhs_cost"] <= 12
    manifest = json.loads((output / "generated.json").read_text())
    files = [
        output / row["path"]
        for row in manifest["files"]
        if row["path"].endswith((".v", ".sv"))
    ]
    _ok(
        _run(
            [
                "slang",
                "--top",
                manifest["root_rtl_name"],
                *map(str, sorted(files, key=lambda path: path.name != "design_top.sv")),
            ]
        )
    )
    rtl = "\n".join(path.read_text() for path in files)
    assert not re.search(r"\b(?:pyc_net|predicate|value|argument|capture)_\d+\b", rtl)
    return output, plans, rtl


def test_binding_rename_and_dead_computation_do_not_change_the_presentation_graph(
    tmp_path,
):
    signatures = []
    for index, (left, right, local, extra) in enumerate(
        [
            ("left", "right", "combined", ""),
            ("input_with_a_longer_authored_name", "incoming", "packed", ""),
            ("left", "right", "combined", "    unused = (left ^ right) + 3\n"),
        ]
    ):
        directory = tmp_path / str(index)
        directory.mkdir()
        text = (
            f"import pycircuit as ac\n@ac.module\ndef Probe({left}: ac.u8, {right}: ac.u8, enable: ac.u1) -> tuple[ac.u8, ac.u8]:\n"
            + extra
            + f"    {local} = ({left} + {right}) ^ ({left} - {right})\n"
            + "    saved: ac.u8 = 0\n    @ac.rule\n    def update() -> None:\n"
            + f"        if enable:\n            saved = {local}\n    return saved, {local}\n"
        )
        output, plans, rtl = _hardware(directory, text)
        signatures.append(
            Counter(
                (
                    node["kind"],
                    node["uses"],
                    node["arity"],
                    node["materialization"],
                    node["rhs_cost"],
                )
                for plan in plans
                for node in plan["values"]
                if node["live"]
            )
        )
        assert len(re.findall(r"\s\+\s", rtl.split("endpackage", 1)[-1])) == 1
        assert len(re.findall(r"\s-\s", rtl.split("endpackage", 1)[-1])) == 1
        body = "rst=1;step();rst=0;\n"
        saved = 0
        for value in range(16):
            a, b, enable = value * 17 % 256, value * 31 % 256, value % 3 != 0
            mixed = ((a + b) % 256) ^ ((a - b) % 256)
            body += f"{left}={a};{right}={b};enable={int(enable)};#1;"
            body += f"if(result_0!==8'd{saved} || result_1!==8'd{mixed})$fatal(1,\"data\");step();\n"
            if enable:
                saved = mixed
        simulate(output, directory, body)
    assert signatures[0] == signatures[1] == signatures[2]


def test_deep_control_has_a_complete_bounded_plan_and_preserves_unknowns(tmp_path):
    # Native final IR isolates presentation depth from the source publication
    # summary's separate admission limit; neither budget is changed.
    body = ""
    previous = "%flag"
    for index in range(140):
        body += f'%v{index} = "ac.bits.binary"({previous}, %gate) {{opcode = "xor"}} : (!b1, !b1) -> !b1\n'
        previous = f"%v{index}"
    body += f'"ac.yield"({previous}) : (!b1) -> ()\n'
    rtl, plans = _native_graph(
        tmp_path, body, "!b1, !b1", "%flag: !b1, %gate: !b1", "!b1", ["flag", "gate"]
    )
    assert sum(plan["live_values"] for plan in plans) > 128
    checks = ""
    for flag, gate in ((a, b) for a in "01xz" for b in "01xz"):
        expected = flag if flag in "01" and gate in "01" else "x"
        checks += f"flag=1'b{flag};gate=1'b{gate};#1;if(result!==1'b{expected})$fatal(1,\"four-state\");\n"
    _native_simulate(
        tmp_path,
        rtl,
        "logic flag,gate;wire result;design_top dut(.flag(flag),.gate(gate),.result(result));",
        checks,
    )


def test_auxiliary_read_result_is_planned_without_an_authored_binding(tmp_path):
    _, plans, rtl = _hardware(
        tmp_path,
        "import pycircuit as ac\n@ac.module\n"
        "def Probe(values: ac.table[3, ac.u8], index: ac.u1) -> ac.u8:\n"
        "    return values[index]\n",
    )
    predicates = [
        row for plan in plans for row in plan["values"] if row["kind"] == "in_range"
    ]
    assert len(predicates) == 1
    assert predicates[0]["emitted"] and predicates[0]["uses"] == 1
    assert predicates[0]["context"] == "index_in_range"
    assert "index_in_range ? values[$unsigned(index)] : 'x" in rtl


def _native_graph(tmp_path, body, inputs, arguments, output, names, record=False):
    literal = '#ac.static_expr<{kind = "literal", value = {kind = "integer", value = #ac.math_int<1>}, origin = {site = {definition = @Probe, ast_path = []}, expansion = []}, location = {path = "probe.py", line = 1 : i64, column = 1 : i64, end_line = 1 : i64, end_column = 2 : i64}}>'
    text = f'#w1 = {literal}\n!b1 = !ac.bits<#w1>\n!pair = !ac.struct<"Pair">\n'
    text += 'module attributes {ac.stage = "final", ac.source_units = [{package = "", path = "probe.py"}]} {\n'
    if record:
        text += 'ac.struct "Pair" fields [{name = "first", type = !b1}, {name = "second", type = !b1}]\n'
    text += '"ac.module"() ({\n^bb0(' + arguments + "):\n" + body
    text += (
        '}) {sym_name = "Probe", source_owner = {package = "", path = "probe.py"}, parameters = [], type_parameters = [], function_type = ('
        + inputs
        + ") -> ("
        + output
        + "), input_names = "
        + json.dumps(names)
        + ', output_names = ["result"]} : () -> ()\n'
    )
    text += '"ac.system"() {entry = {callee = @Probe, parameters = [], type_arguments = []}, domain = "default"} : () -> ()\n}\n'
    source = tmp_path / "graph.mlir"
    source.write_text(text)
    command = [
        os.environ["PYCIRCUIT_EMITTER"],
        str(source),
        "--target",
        "verilog",
        "--rtl-mode",
        "synthesis",
    ]
    data = json.loads(_ok(_run(command)))
    plans = [row["presentation_plan"] for row in data["rtl_value_names"]["modules"]]
    assert plans and all(plan["complete"] for plan in plans)
    for plan in plans:
        for node in plan["values"]:
            if node["arity"] <= 3:
                assert node["rhs_cost"] <= 12
    rtl = _ok(_run(command + ["--format", "source"]))
    assert not re.search(r"\b(?:pyc_net|predicate|value|argument|capture)_\d+\b", rtl)
    return rtl, plans


def _native_simulate(tmp_path, rtl, declarations, checks):
    source, bench, binary = (
        tmp_path / "design.sv",
        tmp_path / "tb.sv",
        tmp_path / "test.vvp",
    )
    source.write_text(rtl)
    bench.write_text(
        "module tb;"
        + declarations
        + "initial begin "
        + checks
        + "$finish;end endmodule\n"
    )
    _ok(_run(["slang", "--top", "design_top", str(source)]))
    _ok(
        _run(
            [
                "iverilog",
                "-g2012",
                "-s",
                "tb",
                "-o",
                str(binary),
                str(source),
                str(bench),
            ]
        )
    )
    _ok(_run(["vvp", str(binary)]))


def test_field_sensitive_graphs_do_not_become_false_value_cycles(tmp_path):
    body = '%first = "ac.struct.get"(%pair) {field = "second"} : (!pair) -> !b1\n'
    body += '%pair = "ac.struct.create"(%first, %flag) : (!b1, !b1) -> !pair\n'
    body += '"ac.yield"(%pair) : (!pair) -> ()\n'
    rtl, plans = _native_graph(
        tmp_path, body, "!b1", "%flag: !b1", "!pair", ["flag"], record=True
    )
    assert any(node["coupled_fields"] for plan in plans for node in plan["values"])
    checks = ""
    for flag in "01xz":
        checks += (
            f"flag=1'b{flag};#1;if(result!==2'b{flag}{flag})$fatal(1,\"fields\");\n"
        )
    _native_simulate(
        tmp_path,
        rtl,
        "logic flag;wire [1:0] result;design_top dut(.flag(flag),.result(result));",
        checks,
    )
