"""Static Method ownership, version, width and atomic-enable conformance."""

import json
import re

import pytest
from test_source_system_execution import _cli, _ok

SOURCE = """import pycircuit as ac
@ac.module
def Counter():
    count: ac.u8 = 0
    @ac.method(guard=lambda amount: count < 240)
    def add(amount: ac.u8) -> ac.u8:
        count = count + amount
        return count
@ac.module
def Joint(first: ac.u8, second: ac.u8, enable: ac.u1) -> tuple[ac.u8, ac.u8]:
    left = Counter()
    right = Counter()
    @ac.rule(guard=lambda: enable)
    def update() -> tuple[ac.u8, ac.u8]:
        a = left.add(first)
        b = right.add(second)
        return a, b
    return update
@ac.module
def Sequential(first: ac.u8, second: ac.u8) -> tuple[ac.u8, ac.u8]:
    counter = Counter()
    @ac.rule
    def update() -> tuple[ac.u8, ac.u8]:
        a = counter.add(first)
        b = counter.add(second)
        return a, b
    return update
@ac.module
def Arithmetic():
    @ac.method
    def narrow(first: ac.u4, second: ac.u4) -> ac.u8:
        small: ac.u4 = first + second
        wide: ac.u8 = small
        return wide
    @ac.method
    def shared(value: ac.u8) -> tuple[ac.u8, ac.u8]:
        common = value + 1
        return common, common
    @ac.method
    def identity(value: ac.u8) -> ac.u8:
        return value
@ac.module
def Width(first: ac.u4, second: ac.u4) -> ac.u8:
    arithmetic = Arithmetic()
    @ac.rule
    def compute() -> ac.u8:
        return arithmetic.narrow(first, second)
    return compute
@ac.module
def Sharing(value: ac.u8) -> tuple[ac.u8, ac.u8]:
    arithmetic = Arithmetic()
    @ac.rule
    def compute() -> tuple[ac.u8, ac.u8]:
        first, second = arithmetic.shared(value)
        return first, second
    return compute
@ac.module
def CrossSharing(value: ac.u8) -> tuple[ac.u8, ac.u8]:
    left = Arithmetic()
    right = Arithmetic()
    @ac.rule
    def compute() -> tuple[ac.u8, ac.u8]:
        a, unused_a = left.shared(value)
        b, unused_b = right.shared(value)
        return a, b
    return compute
@ac.module
def SharedAncestor(value: ac.u8) -> tuple[ac.u8, ac.u8]:
    left = Arithmetic()
    right = Arithmetic()
    @ac.rule
    def compute() -> tuple[ac.u8, ac.u8]:
        common = value + 1
        a = left.identity(common)
        b = right.identity(common)
        return a, b
    return compute
"""


@pytest.fixture(scope="module")
def ownership_views(tmp_path_factory):
    root = tmp_path_factory.mktemp("rtl-ownership")
    source = root / "owners.py"
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
            "rtl_ownership",
            "-o",
            str(unit),
        )
    )
    views = {}
    for name in (
        "Joint",
        "Sequential",
        "Width",
        "Sharing",
        "CrossSharing",
        "SharedAncestor",
    ):
        final = root / (name + ".ac")
        _ok(
            _cli(
                "link",
                str(unit),
                "--top",
                "rtl_ownership.owners." + name,
                "-o",
                str(final),
            )
        )
        for mode in ("managed", "physical", "synthesis"):
            output = root / (name + "-" + mode)
            _ok(
                _cli(
                    "emit",
                    str(final),
                    "--target",
                    "verilog",
                    "--rtl-mode",
                    mode,
                    "-o",
                    str(output),
                )
            )
            text = "\n".join(
                path.read_text() for path in (output / "sources").rglob("*.v")
            )
            views[name, mode] = text, json.loads(
                (output / "rtl-names.json").read_text()
            )
    return views


def modules(text):
    return dict(re.findall(r"(?ms)^module (\S+)\b(.*?^endmodule\b)", text))


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_two_receivers_keep_one_adder_and_one_storage_each(ownership_views, mode):
    text, _ = ownership_views["Joint", mode]
    units = modules(text)
    counters = [body for name, body in units.items() if name.startswith("Counter")]
    assert len(counters) == 2
    assert all(len(re.findall(r"\s\+\s", body)) == 1 for body in counters)
    assert all(body.count("always_ff") == 1 for body in counters)
    assert not re.search(r"\s\+\s|always_ff", units["Joint"])
    # Both actual receivers retain the exact same outer Rule's final enable.
    controls = re.findall(r"\.count_enable\(([^\n]+)\)", units["Joint"])
    assert len(controls) == 2 and controls[0] == controls[1]


def test_sequential_calls_keep_candidate_version_dependency(ownership_views):
    _, mapping = ownership_views["Sequential", "synthesis"]
    owner = next(
        module
        for module in mapping["modules"]
        if module["source_symbol"].endswith(".Counter")
    )
    nodes = {node["optimized_value"]: node for node in owner["values"]}
    adders = [
        node
        for node in nodes.values()
        if node["opcode"] == "ac.bits.binary"
        and node["rtl_expression"]
        and "#ac.math_int<8>" in node["type"]
    ]
    assert len(adders) == 2

    def reaches(start, target):
        pending, seen = list(nodes[start]["operands"]), set()
        while pending:
            current = pending.pop()
            if current == target:
                return True
            if current not in seen:
                seen.add(current)
                pending.extend(nodes[current]["operands"])
        return False

    first, second = [node["optimized_value"] for node in adders]
    assert reaches(first, second) or reaches(second, first)


def test_narrow_addition_still_wraps_before_widening(ownership_views):
    text, mapping = ownership_views["Width", "synthesis"]
    units = modules(text)
    arithmetic = units["Arithmetic"]
    assert len(re.findall(r"\s\+\s", arithmetic)) == 1
    assert "logic [3:0] \\small " in arithmetic and "logic [7:0] wide" in arithmetic
    assert not re.search(r"\s\+\s", units["Width"])
    owner = next(
        module
        for module in mapping["modules"]
        if module["source_symbol"].endswith(".Arithmetic")
    )
    assert any(
        node["opcode"] == "ac.bits.binary" and "#ac.math_int<4>" in node["type"]
        for node in owner["values"]
    )


@pytest.mark.parametrize("mode", ["managed", "physical", "synthesis"])
def test_shared_method_result_is_computed_once(ownership_views, mode):
    text, _ = ownership_views["Sharing", mode]
    assert len(re.findall(r"\s\+\s", text)) == 1


def test_partitioned_navigation_keeps_all_operand_ids_bound(ownership_views):
    for name in ("Joint", "Sequential", "Width", "Sharing"):
        _, mapping = ownership_views[name, "synthesis"]
        for module in mapping["modules"]:
            ids = {node["optimized_value"] for node in module["values"]}
            assert all(
                operand in ids
                for node in module["values"]
                for operand in node["operands"]
            )
            for binding in mapping["bindings"]:
                if binding["module"] == module["rtl_module"]:
                    assert binding["optimized_value"] in ids


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_distinct_cross_receiver_operators_are_not_duplicated(ownership_views, mode):
    text, mapping = ownership_views["CrossSharing", mode]
    # The baseline has two distinct optimized operators for these two calls.
    assert len(re.findall(r"\s\+\s", text)) == 2
    assert not re.search(r"\s\+\s", modules(text)["CrossSharing"])


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_one_shared_ancestor_calculation_feeds_both_receivers(ownership_views, mode):
    text, _ = ownership_views["SharedAncestor", mode]
    assert len(re.findall(r"\s\+\s", text)) == 1
    assert len(re.findall(r"\s\+\s", modules(text)["SharedAncestor"])) == 1
