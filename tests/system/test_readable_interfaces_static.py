"""Typed private-interface projection; native emission and static metadata only."""

import json
import os
import re

import pytest
from test_source_system_execution import _ok, _run


@pytest.fixture(scope="module")
def interface_views(tmp_path_factory):
    root = tmp_path_factory.mktemp("readable-interfaces-native")
    static = '#ac.static_expr<{kind = "literal", value = {kind = "integer", value = #ac.math_int<8>}, origin = {site = {definition = @top, ast_path = []}, expansion = []}, location = {path = "top.py", line = 1 : i64, column = 1 : i64, end_line = 1 : i64, end_column = 2 : i64}}>'
    result = {}
    for case in ("constructed", "renamed", "public", "projected"):
        leaf = "Slice" if case == "renamed" else "Leaf"
        first, second = ("left", "right") if case == "renamed" else ("first", "second")
        inputs = "!pair" if case == "projected" else "!b8, !b8"
        arguments = "%pair: !pair" if case == "projected" else "%a: !b8, %b: !b8"
        port_names = ["pair"] if case == "projected" else ["a", "b"]
        if case == "projected":
            body = (
                f'%a = "ac.struct.get"(%pair) {{field = "{first}"}} : (!pair) -> !b8\n'
            )
            body += (
                f'%b = "ac.struct.get"(%pair) {{field = "{second}"}} : (!pair) -> !b8\n'
            )
        else:
            body = '%pair = "ac.struct.create"(%a, %b) : (!b8, !b8) -> !pair\n'
        body += (
            '%unused = "ac.bits.binary"(%a, %b) {opcode = "add"} : (!b8, !b8) -> !b8\n'
        )
        body += '%difference = "ac.bits.binary"(%a, %b) {opcode = "sub"} : (!b8, !b8) -> !b8 loc(fused<{ac.source_name = "difference", scope = "leaf", index = 0 : i64, result = true}>[unknown])\n'
        private = (
            ""
            if case == "public"
            else ", ac.transaction_wiring = {states = [], incoming = [], writers = []}, ac.internal_ports = {source_inputs = "
            + str(len(port_names))
            + " : i64, source_outputs = 1 : i64, root_inputs = []}"
        )
        text = (
            "#w8 = "
            + static
            + '\n!b8 = !ac.bits<#w8>\n!pair = !ac.struct<"Pair">\nmodule attributes {ac.stage = "final", ac.source_units = [{package = "", path = "leaf.py"}, {package = "", path = "top.py"}]} {\n'
        )
        text += (
            'ac.struct "Pair" fields [{name = "'
            + first
            + '", type = !b8}, {name = "'
            + second
            + '", type = !b8}]\n'
        )
        text += '"ac.module"() ({\n^bb0(' + arguments + "):\n" + body
        text += '"ac.yield"(%pair, %a, %b, %unused, %difference) : (!pair, !b8, !b8, !b8, !b8) -> ()\n'
        text += (
            '}) {sym_name = "'
            + leaf
            + '", source_owner = {package = "", path = "leaf.py"}, parameters = [], type_parameters = [], function_type = ('
            + inputs
            + ") -> (!pair, !b8, !b8, !b8, !b8), input_names = "
            + json.dumps(port_names)
            + ', output_names = ["result", "private_a", "private_b", "private_unused", "private_difference"]'
            + private
            + "} : () -> ()\n"
        )
        text += '"ac.module"() ({\n^bb0(%a: !b8, %b: !b8, %c: !b8):\n'
        text += '%pair = "ac.struct.create"(%a, %b) : (!b8, !b8) -> !pair\n'
        for index, name in enumerate(("lane0", "lane1", "lane2")):
            actuals = (
                "%pair"
                if case == "projected"
                else "%" + "abc"[index] + ", %" + "bca"[index]
            )
            text += (
                f'%r{index}:5 = "ac.instance"('
                + actuals
                + ') {instance_name = "'
                + name
                + '", callee = @'
                + leaf
                + ', parameters = [], type_arguments = [], occurrence = {site = {definition = @top, ast_path = [{kind = "field", name = "body"}, {kind = "index", value = '
                + str(index)
                + " : i64}]}, expansion = []}} : ("
                + inputs
                + ") -> (!pair, !b8, !b8, !b8, !b8)\n"
            )
        text += '%twice = "ac.bits.binary"(%r0#4, %r0#4) {opcode = "add"} : (!b8, !b8) -> !b8\n'
        text += '"ac.yield"(%r0#0, %r1#0, %r2#0, %r0#1, %r1#2, %twice) : (!pair, !pair, !pair, !b8, !b8, !b8) -> ()\n'
        text += '}) {sym_name = "top", source_owner = {package = "", path = "top.py"}, parameters = [], type_parameters = [], function_type = (!b8, !b8, !b8) -> (!pair, !pair, !pair, !b8, !b8, !b8), input_names = ["a", "b", "c"], output_names = ["first", "second", "third", "field_a", "field_b", "twice"]} : () -> ()\n'
        text += '"ac.system"() {entry = {callee = @top, parameters = [], type_arguments = []}, domain = "default"} : () -> ()\n}\n'
        source = root / (case + ".mlir")
        source.write_text(text)
        for mode in ("physical", "synthesis"):
            command = [
                os.environ["PYCIRCUIT_EMITTER"],
                str(source),
                "--target",
                "verilog",
                "--rtl-mode",
                mode,
            ]
            data = json.loads(_ok(_run(command)))
            rtl = _ok(_run(command + ["--format", "source"]))
            (root / (case + "-" + mode + ".json")).write_text(json.dumps(data))
            (root / (case + "-" + mode + ".sv")).write_text(rtl)
            result[case, mode] = data, rtl, leaf
    return result


@pytest.mark.parametrize("case", ["constructed", "renamed", "projected"])
def test_private_aliases_reuse_the_original_public_record_fields(interface_views, case):
    data, rtl, leaf = interface_views[case, "synthesis"]
    module = next(
        row for row in data["rtl_value_names"]["modules"] if row["rtl_module"] == leaf
    )
    outputs = module["interface"]["outputs"]
    assert outputs[1]["omitted"] and outputs[2]["omitted"]
    assert outputs[1]["projection_output"] == outputs[2]["projection_output"] == 0
    assert outputs[1]["projection_fields"] == ["left" if case == "renamed" else "first"]
    assert outputs[2]["projection_fields"] == [
        "right" if case == "renamed" else "second"
    ]
    assert re.search(r"assign field_a = lane_result\[0\]\.(?:first|left);", rtl)
    assert re.search(r"assign field_b = lane_result\[1\]\.(?:second|right);", rtl)
    assert "lane_private_a" not in rtl and "lane_private_b" not in rtl


def test_unused_private_transport_is_removed_and_used_computation_remains_shared(
    interface_views,
):
    data, rtl, leaf = interface_views["constructed", "synthesis"]
    module = next(
        row for row in data["rtl_value_names"]["modules"] if row["rtl_module"] == leaf
    )
    assert module["interface"]["outputs"][3]["omitted"]
    assert not module["interface"]["outputs"][4]["omitted"]
    assert len(re.findall(r"\s-\s", rtl.split("endpackage", 1)[-1])) == 1
    assert "lane_difference[0]" in rtl
    assert "lane_private_unused" not in rtl


def test_declared_source_outputs_are_preserved_even_when_their_values_are_unused(
    interface_views,
):
    data, rtl, leaf = interface_views["public", "synthesis"]
    module = next(
        row for row in data["rtl_value_names"]["modules"] if row["rtl_module"] == leaf
    )
    assert not any(row["omitted"] for row in module["interface"]["outputs"])
    assert module["interface"]["source_outputs"] == 5
    assert "lane_private_unused" in rtl


@pytest.mark.parametrize("case", ["constructed", "renamed", "projected", "public"])
def test_physical_check_interfaces_keep_the_existing_port_inventory(
    interface_views, case
):
    data, rtl, leaf = interface_views[case, "physical"]
    module = next(
        row for row in data["rtl_value_names"]["modules"] if row["rtl_module"] == leaf
    )
    assert not any(row["omitted"] for row in module["interface"]["outputs"])
    assert rtl.count("." + module["interface"]["outputs"][3]["rtl_port"] + "(") == 3
