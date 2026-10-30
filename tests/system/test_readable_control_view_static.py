"""Control presentation: independent finite truth-table checks, no design run."""

import itertools
import json
import os
import re

import pytest
from test_source_system_execution import _ok, _run


def truth(operation, inputs):
    a, *rest = inputs
    b = rest[0] if rest else None
    if operation == "not":
        return {0: 1, 1: 0, 2: 2, 3: 2}[a]
    if operation in ("and", "or", "xor"):
        if operation == "and" and 0 in inputs:
            return 0
        if operation == "or" and 1 in inputs:
            return 1
        if max(inputs) > 1:
            return 2
        return {"and": min(inputs), "or": max(inputs), "xor": a ^ b}[operation]
    if operation.startswith("compare:"):
        predicate = operation.split(":")[1]
        if predicate == "case_eq":
            return int(a == b)
        if max(inputs) > 1:
            return 2
        if predicate in ("eq", "ne"):
            return int((a == b) if predicate == "eq" else (a != b))
        if predicate.startswith("s"):
            a, b = (-1 if bit else 0 for bit in (a, b))
        return int(
            {"lt": a < b, "le": a <= b, "gt": a > b, "ge": a >= b}[predicate[1:]]
        )
    if operation == "require":
        a, b = b, a
        rest = [b, 1]
    if a in (0, 1):
        return rest[0 if a else 1]
    return rest[0] if rest[0] == rest[1] else 2


def check_control_views(module):
    """Check each projection using conservative operand domains, independently."""
    views = {row["value"]: row for row in module["control_views"]}
    checked, projected, tuples, incomplete = 0, 0, 0, 0
    for key, row in views.items():
        operation = row["operation"]
        assert 0 < row["domain"] < 16
        if operation.startswith("literal:"):
            literal = operation.split(":", 1)[1]
            bit = "01xz".index(literal[-1])
            assert row["domain"] == 1 << bit
            assert row["literal"] in (None, bit)
            continue
        if operation == "atom":
            assert (
                row["domain"] == 15 and row["target"] == key and row["literal"] is None
            )
            continue
        if not row["complete"]:
            # A wider comparison is not in the one-bit algebra. Its result is
            # still never Z, and case equality is always known. It cannot be
            # forwarded or folded through an unexamined boundary.
            assert row["target"] == key and row["literal"] is None
            assert operation.startswith("compare:") or row["domain"] == 15, (
                module["rtl_module"],
                row,
            )
            assert row["domain"] in (3, 7, 15)
            incomplete += 1
            continue
        children = [views[value] for value in row["inputs"]]
        domains = [
            [bit for bit in range(4) if child["domain"] & (1 << bit)]
            for child in children
        ]
        observed = 0
        for bits in itertools.product(*domains):
            if any(
                left["literal"] is None
                and right["literal"] is None
                and left["target"] == right["target"]
                and bits[i] != bits[j]
                for i, left in enumerate(children)
                for j, right in enumerate(children[:i])
            ):
                continue
            bit = truth(operation, bits)
            tuples += 1
            observed |= 1 << bit
            if row["literal"] is not None:
                assert bit == row["literal"], (key, row, bits)
            elif row["target"] != key:
                indices = [
                    index
                    for index, child in enumerate(children)
                    if child["target"] == row["target"]
                ]
                assert indices and all(bit == bits[index] for index in indices), (
                    key,
                    row,
                    bits,
                )
        assert observed & ~row["domain"] == 0, (key, row, observed)
        checked += 1
        projected += int(row["literal"] is not None or row["target"] != key)
    return {
        "checked": checked,
        "projected": projected,
        "tuples": tuples,
        "incomplete": incomplete,
    }


def check_fact_proofs(module):
    views = {row["value"]: row for row in module["control_views"]}
    checked, tuples = 0, 0
    for proof in module.get("fact_proofs", []):
        assert proof["domain"] in (1, 2)
        leaves, seen = set(), set()
        pending = [proof["selector"]] + [
            row["value"] for row in proof["assumptions"] + proof["facts"]
        ]
        while pending:
            key = pending.pop()
            if key in seen:
                continue
            seen.add(key)
            row = views[key]
            if row["operation"] == "atom" or not row["complete"]:
                leaves.add(key)
            elif not row["operation"].startswith("literal:"):
                pending.extend(row["inputs"])
        leaves = sorted(leaves)
        assert len(leaves) <= 8, (
            "fact proof enumeration boundary",
            module["rtl_module"],
            len(leaves),
        )
        domains = [
            [bit for bit in range(4) if views[key]["domain"] & (1 << bit)]
            for key in leaves
        ]
        for bits in itertools.product(*domains):
            cache = dict(zip(leaves, bits, strict=False))

            def evaluate(key, cache=cache):
                if key not in cache:
                    row = views[key]
                    if row["operation"].startswith("literal:"):
                        cache[key] = "01xz".index(row["operation"][-1])
                    else:
                        cache[key] = truth(
                            row["operation"],
                            [evaluate(child) for child in row["inputs"]],
                        )
                return cache[key]

            if not all(
                evaluate(row["value"]) == int(row["truth"])
                for row in proof["assumptions"]
            ):
                continue
            tuples += 1
            assert all(
                evaluate(row["value"]) == int(row["truth"]) for row in proof["facts"]
            ), (module["rtl_module"], proof, cache)
            assert 1 << evaluate(proof["selector"]) == proof["domain"], (
                module["rtl_module"],
                proof,
                cache,
            )
        checked += 1
    return {"proofs": checked, "reachable_tuples": tuples}


@pytest.fixture(scope="module")
def control_views(tmp_path_factory):
    root = tmp_path_factory.mktemp("readable-control-native")
    static = '#ac.static_expr<{kind = "literal", value = {kind = "integer", value = #ac.math_int<1>}, origin = {site = {definition = @top, ast_path = []}, expansion = []}, location = {path = "top.py", line = 1 : i64, column = 1 : i64, end_line = 1 : i64, end_column = 2 : i64}}>'
    zero = static.replace("#ac.math_int<1>", "#ac.math_int<0>")
    body = [
        f'%one = "ac.bits.constant"() {{value = {static}}} : () -> !b1',
        f'%zero = "ac.bits.constant"() {{value = {zero}}} : () -> !b1',
    ]
    outputs = []

    def emit(name, operation, inputs, attributes=""):
        body.append(
            f'%{name} = "ac.bits.{operation}"('
            + ", ".join("%" + value for value in inputs)
            + ")"
            + attributes
            + " : ("
            + ", ".join("!b1" for value in inputs)
            + ") -> !b1"
        )
        outputs.append(name)

    emit("constant_mux", "select", ["a", "one", "one"])
    emit("same_mux", "select", ["a", "b", "b"])
    emit("and_z", "binary", ["a", "one"], ' {opcode = "and"}')
    emit("known", "compare", ["a", "one"], ' {predicate = "case_eq"}')
    emit("and_known", "binary", ["known", "one"], ' {opcode = "and"}')
    emit("shared", "binary", ["a", "b"], ' {opcode = "or"}')
    emit("shared_left", "binary", ["shared", "c"], ' {opcode = "and"}')
    emit("shared_right", "binary", ["shared", "c"], ' {opcode = "xor"}')
    emit("inverted", "unary", ["a"], ' {opcode = "not"}')
    emit("and_inverted", "binary", ["inverted", "one"], ' {opcode = "and"}')
    emit("unknown_mux", "select", ["a", "b", "c"])
    for index in range(6):
        emit(
            "guard" + str(index),
            "compare",
            ["b" if index % 2 else "c", "one"],
            ' {predicate = "case_eq"}',
        )
        emit("require" + str(index), "select", ["known", "guard" + str(index), "one"])
        if index:
            emit(
                "checks" + str(index),
                "binary",
                [
                    "require0" if index == 1 else "checks" + str(index - 1),
                    "require" + str(index),
                ],
                ' {opcode = "and"}',
            )
    emit("guarded_data", "select", ["a", "b", "one"])
    emit(
        "guarded_ready", "compare", ["guarded_data", "one"], ' {predicate = "case_eq"}'
    )
    emit("guarded_check", "select", ["known", "guarded_ready", "one"])
    emit("conditioned", "binary", ["checks5", "guarded_check"], ' {opcode = "and"}')
    emit("c_zero", "compare", ["c", "zero"], ' {predicate = "case_eq"}')
    emit("strict_path", "binary", ["known", "c_zero"], ' {opcode = "and"}')
    emit("not_c", "unary", ["c"], ' {opcode = "not"}')
    emit("raw_path", "binary", ["a", "not_c"], ' {opcode = "and"}')
    emit("path_data", "select", ["raw_path", "b", "one"])
    emit("path_ready", "compare", ["path_data", "one"], ' {predicate = "case_eq"}')
    emit("multi_check", "select", ["strict_path", "path_ready", "one"])
    emit("multi_second", "binary", ["multi_check", "known"], ' {opcode = "and"}')
    # Keep only the meaningful roots: intermediates must remain private.
    outputs = outputs[:11] + ["conditioned", "multi_check", "multi_second"]
    types = ", ".join("!b1" for value in outputs)
    source = root / "controls.mlir"
    source.write_text(
        "#w1 = "
        + static
        + "\n!b1 = !ac.bits<#w1>\nmodule {\n"
        + '"ac.module"() ({\n^bb0(%a: !b1, %b: !b1, %c: !b1):\n'
        + "\n".join(body)
        + '\n"ac.yield"('
        + ", ".join("%" + value for value in outputs)
        + ") : ("
        + types
        + ") -> ()\n"
        + '}) {sym_name = "top", source_owner = {package = "", path = "top.py"}, parameters = [], type_parameters = [], '
        + "function_type = (!b1, !b1, !b1) -> ("
        + types
        + '), input_names = ["a", "b", "c"], output_names = '
        + json.dumps(outputs)
        + "} : () -> ()\n"
        + '"ac.system"() {entry = {callee = @top, parameters = [], type_arguments = []}, domain = "default"} : () -> ()\n}\n'
    )
    result = {}
    for mode in ("physical", "synthesis"):
        command = [
            os.environ["PYCIRCUIT_EMITTER"],
            str(source),
            "--target",
            "verilog",
            "--rtl-mode",
            mode,
        ]
        emitted = json.loads(_ok(_run(command)))
        (root / (mode + ".json")).write_text(json.dumps(emitted))
        text = _ok(_run(command + ["--format", "source"]))
        (root / (mode + ".sv")).write_text(text)
        result[mode] = emitted, text
    return result


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_projected_controls_have_independently_checked_four_state_tables(
    control_views, mode
):
    data, text = control_views[mode]
    totals = [
        check_control_views(module) for module in data["rtl_value_names"]["modules"]
    ]
    assert sum(row["projected"] for row in totals) >= 4
    assert "assign constant_mux = 1'b1;" in text
    assert "assign same_mux = b;" in text
    assert re.search(r"assign and_z = .*\ba\b.*;", text)
    assert "&" in next(line for line in text.splitlines() if "assign and_z =" in line)


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_nontrivial_shared_control_is_still_one_producer(control_views, mode):
    text = control_views[mode][1]
    assert len(re.findall(r"\ba\s*\|\s*b\b", text)) == 1
    assert "assign shared_left" in text and "assign shared_right" in text
    assert "a ? b :" in text or "a ? b : c" in text


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_complex_known_requirements_use_a_complete_structured_block(
    control_views, mode
):
    text = control_views[mode][1]
    assert "always_comb begin" in text
    assert re.search(r"always_comb begin\s+\w+ = 1'b1;", text)
    assert "if (" in text
    # Under the known-one test of a, the private selected payload is b. The
    # final ready test must still use case equality, including b = X or Z.
    assert re.search(r"&& \(b === 1'b1\)", text)
    assert not re.search(r"\binitial\b|\balways_ff\b", text)


def test_truth_table_checker_rejects_the_invalid_z_identity():
    bad = {
        "control_views": [
            {
                "value": 0,
                "target": 0,
                "literal": None,
                "domain": 15,
                "operation": "atom",
                "inputs": [],
                "complete": True,
            },
            {
                "value": 1,
                "target": 1,
                "literal": 1,
                "domain": 2,
                "operation": "literal:1'b1",
                "inputs": [],
                "complete": True,
            },
            {
                "value": 2,
                "target": 0,
                "literal": None,
                "domain": 7,
                "operation": "and",
                "inputs": [0, 1],
                "complete": True,
            },
        ]
    }
    with pytest.raises(AssertionError):
        check_control_views(bad)


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_multileaf_path_facts_keep_a_shared_conditional_requirement(
    control_views, mode
):
    data, text = control_views[mode]
    assert re.search(r"assign b_check(?:_\d+)? = .*\? \(b === 1'b1\) : 1'b1;", text)
    assert any(
        module.get("fact_proofs") for module in data["rtl_value_names"]["modules"]
    )
    assert (
        sum(
            check_fact_proofs(module)["proofs"]
            for module in data["rtl_value_names"]["modules"]
        )
        > 0
    )


def test_fact_checker_rejects_a_missing_condition_on_the_other_leaf():
    rows = [
        {
            "value": key,
            "target": key,
            "literal": None,
            "domain": 15,
            "operation": "atom",
            "inputs": [],
            "complete": True,
        }
        for key in (0, 1)
    ]
    rows += [
        {
            "value": 2,
            "target": 2,
            "literal": 1,
            "domain": 2,
            "operation": "literal:1'b1",
            "inputs": [],
            "complete": True,
        },
        {
            "value": 3,
            "target": 3,
            "literal": None,
            "domain": 3,
            "operation": "compare:case_eq",
            "inputs": [0, 2],
            "complete": True,
        },
        {
            "value": 4,
            "target": 4,
            "literal": None,
            "domain": 7,
            "operation": "and",
            "inputs": [0, 1],
            "complete": True,
        },
    ]
    module = {
        "rtl_module": "bad",
        "control_views": rows,
        "fact_proofs": [
            {
                "selector": 4,
                "domain": 2,
                "assumptions": [{"value": 3, "truth": True}],
                "facts": [{"value": 0, "truth": True}],
            }
        ],
    }
    with pytest.raises(AssertionError):
        check_fact_proofs(module)
