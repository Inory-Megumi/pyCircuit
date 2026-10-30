"""Native module-interface array conformance, independent of example names."""

import json
import os
import re

import pytest
from test_source_system_execution import _ok, _run


@pytest.fixture(scope="module")
def instance_arrays(tmp_path_factory):
    root = tmp_path_factory.mktemp("readable-instance-arrays-native")
    width = '#ac.static_expr<{kind = "literal", value = {kind = "integer", value = #ac.math_int<8>}, origin = {site = {definition = @top, ast_path = []}, expansion = []}, location = {path = "top.py", line = 1 : i64, column = 1 : i64, end_line = 1 : i64, end_column = 2 : i64}}>'
    leaf = """"ac.module"() ({
^bb0(%x: !b8, %amount: !b8):
    %sum = "ac.bits.binary"(%x, %amount) {opcode = "add"} : (!b8, !b8) -> !b8
    "ac.yield"(%sum) : (!b8) -> ()
}) {sym_name = "LEAF", source_owner = {package = "", path = "leaf.py"}, parameters = [], type_parameters = [], function_type = (!b8, !b8) -> !b8, input_names = ["x", "amount"], output_names = ["result"]} : () -> ()
"""
    results = {}
    for case in ("regular", "two", "heterogeneous", "collision", "keyword"):
        count = 2 if case == "two" else 3
        body = [
            '%amount = "ac.bits.binary"(%a, %b) {opcode = "add"} : (!b8, !b8) -> !b8'
        ]
        instances = (
            ("cell0", "cell1", "cell2")
            if case == "keyword"
            else ("alpha", "gamma", "omega")
        )
        for index, name in enumerate(instances[:count]):
            callee = "Other" if case == "heterogeneous" and index == 2 else "Leaf"
            body.append(
                f'%r{index} = "ac.instance"(%'
                + "abc"[index]
                + ', %amount) {instance_name = "'
                + name
                + '", callee = @'
                + callee
                + ', parameters = [], type_arguments = [], occurrence = {site = {definition = @top, ast_path = [{kind = "field", name = "body"}, {kind = "index", value = '
                + str(index)
                + " : i64}]}, expansion = []}} : (!b8, !b8) -> !b8"
            )
        types = ", ".join("!b8" for index in range(count))
        input_name = "Leaf_instances_result" if case == "collision" else "c"
        # The SSA input name can differ from its actual exported port spelling.
        source = root / (case + ".mlir")
        source.write_text(
            "#w8 = "
            + width
            + "\n!b8 = !ac.bits<#w8>\nmodule {\n"
            + leaf.replace("LEAF", "Leaf")
            + leaf.replace("LEAF", "Other")
            + '"ac.module"() ({\n^bb0(%a: !b8, %b: !b8, %c: !b8):\n'
            + "\n".join(body)
            + '\n"ac.yield"('
            + ", ".join("%r" + str(index) for index in range(count))
            + ") : ("
            + types
            + ") -> ()\n"
            + '}) {sym_name = "top", source_owner = {package = "", path = "top.py"}, parameters = [], type_parameters = [], '
            + "function_type = (!b8, !b8, !b8) -> ("
            + types
            + '), input_names = ["a", "b", "'
            + input_name
            + '"], output_names = '
            + json.dumps(["result" + str(index) for index in range(count)])
            + "} : () -> ()\n"
            + '"ac.system"() {entry = {callee = @top, parameters = [], type_arguments = []}, domain = "default"} : () -> ()\n}\n'
        )
        command = [
            os.environ["PYCIRCUIT_EMITTER"],
            str(source),
            "--target",
            "verilog",
            "--rtl-mode",
            "synthesis",
        ]
        data = json.loads(_ok(_run(command)))
        text = _ok(_run(command + ["--format", "source"]))
        (root / (case + ".json")).write_text(json.dumps(data))
        (root / (case + ".sv")).write_text(text)
        results[case] = data, text
    return results


def test_regular_instances_use_typed_arrays_and_generate_without_name_patterns(
    instance_arrays,
):
    text = instance_arrays["regular"][1]
    assert "wire logic [7:0] Leaf_instances_result [0:2];" in text
    assert "for (genvar Leaf_instances_index = 0;" in text
    assert ".result(Leaf_instances_result[Leaf_instances_index])" in text
    assert all(f".unit_inst: {name}." in text for name in ("alpha", "gamma", "omega"))
    assert all(
        f"assign result{index} = Leaf_instances_result[{index}];" in text
        for index in range(3)
    )


def test_shared_computation_and_uniform_connections_are_not_replicated(instance_arrays):
    text = instance_arrays["regular"][1]
    assert len(re.findall(r"\s\+\s", text)) == 2
    assert ".amount(" in text
    assert not re.search(r"wire .*Leaf_instances_amount", text)
    data = instance_arrays["regular"][0]
    parent = next(
        module
        for module in data["rtl_value_names"]["modules"]
        if module["rtl_module"] == "top"
    )
    assert [row["source_name"] for row in parent["allocations"]] == [
        "alpha",
        "gamma",
        "omega",
    ]
    assert [row["rtl_name"] for row in parent["allocations"]] == [
        f"Leaf_instances[{index}].unit_inst" for index in range(3)
    ]


@pytest.mark.parametrize("case", ["two", "heterogeneous"])
def test_nonmatching_callees_and_small_groups_keep_the_existing_occurrences(
    instance_arrays, case
):
    text = instance_arrays[case][1]
    assert "for (genvar" not in text
    assert "Leaf alpha (" in text and "Leaf gamma (" in text


def test_array_signal_allocation_respects_existing_ports(instance_arrays):
    text = instance_arrays["collision"][1]
    assert "input wire logic [7:0] Leaf_instances_result" in text
    assert "wire logic [7:0] Leaf_instances_result_1 [0:2];" in text


def test_keyword_group_stems_generate_plain_signal_names(instance_arrays):
    text = instance_arrays["keyword"][1]
    assert "begin : cell_signal" in text
    assert "cell_signal_x" in text
    assert not re.search(r"\\|\bpyc_[0-9a-f]+\b", text)
