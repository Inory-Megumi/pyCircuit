"""Read-only RTL ownership paths and original source transaction conformance."""

import json
import os
import re
from copy import deepcopy

import pytest
from test_source_system_execution import _cli, _ok, _run

SOURCE = """import pycircuit as ac
@ac.module
def Counter():
    count: ac.u8 = 0
    @ac.method
    def add(amount: ac.u8) -> ac.u8:
        count = count + amount
        return count
@ac.module
def Bridge():
    counter = Counter()
    @ac.method
    def add(amount: ac.u8) -> ac.u8:
        return counter.add(amount)
@ac.module
def Cluster():
    bridge = Bridge()
    @ac.method
    def add(amount: ac.u8) -> ac.u8:
        return bridge.add(amount)
@ac.module
def Deep(amount: ac.u8) -> ac.u8:
    cluster = Cluster()
    @ac.rule
    def update() -> ac.u8:
        return cluster.add(amount)
    return update
@ac.module
def Sequential(first: ac.u8, second: ac.u8) -> tuple[ac.u8, ac.u8]:
    bridge = Bridge()
    @ac.rule
    def update() -> tuple[ac.u8, ac.u8]:
        before = bridge.add(first)
        after = bridge.add(second)
        return before, after
    return update
@ac.module
def Independent(amount: ac.u8) -> tuple[ac.u8, ac.u8]:
    left = Bridge()
    right = Bridge()
    @ac.rule
    def update() -> tuple[ac.u8, ac.u8]:
        shared = amount + 1
        first = left.add(shared)
        second = right.add(shared)
        return first, second
    return update
@ac.module
def Biased():
    counter = Counter()
    @ac.method
    def add(amount: ac.u8) -> ac.u8:
        biased = amount + 2
        return counter.add(biased)
@ac.module
def Reused(first: ac.u8, second: ac.u8) -> tuple[ac.u8, ac.u8]:
    left = Biased()
    right = Biased()
    @ac.rule
    def update() -> tuple[ac.u8, ac.u8]:
        a = left.add(first)
        b = right.add(second)
        return a, b
    return update
"""


@pytest.fixture(scope="module")
def hierarchy_views(tmp_path_factory):
    root = tmp_path_factory.mktemp("readable-hierarchy")
    source = root / "hierarchy.py"
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
            "readable_hierarchy",
            "-o",
            str(unit),
        )
    )
    result = {}
    for name in ("Deep", "Sequential", "Independent", "Reused"):
        final = root / (name + ".ac")
        _ok(
            _cli(
                "link",
                str(unit),
                "--top",
                "readable_hierarchy.hierarchy." + name,
                "-o",
                str(final),
            )
        )
        for mode in ("physical", "synthesis"):
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
            result[name, mode] = text, json.loads(
                (output / "rtl-names.json").read_text()
            )
    return result


def modules(text):
    return dict(re.findall(r"(?ms)^module (\S+)\b(.*?^endmodule\b)", text))


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_transitive_receiver_keeps_the_original_adder_with_its_storage(
    hierarchy_views, mode
):
    text, mapping = hierarchy_views["Deep", mode]
    units = modules(text)
    assert len(re.findall(r"\s\+\s", text)) == 1
    assert len(re.findall(r"\s\+\s", units["Counter"])) == 1
    assert units["Counter"].count("always_ff") == 1
    assert not any(
        re.search(r"\s\+\s|always_ff", body)
        for name, body in units.items()
        if name != "Counter"
    )
    assert not any(
        row.get("reason") == "receiver requires a transitive partition"
        for row in mapping["ownership_notes"]
    )


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_sequential_deep_calls_preserve_both_candidate_versions(hierarchy_views, mode):
    text, _ = hierarchy_views["Sequential", mode]
    units = modules(text)
    assert len(re.findall(r"\s\+\s", text)) == 2
    assert len(re.findall(r"\s\+\s", units["Counter"])) == 2
    assert units["Counter"].count("always_ff") == 1
    assert not re.search(r"\s\+\s|always_ff", units["Sequential"])


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_two_deep_receivers_keep_the_shared_ancestor_once(hierarchy_views, mode):
    text, _ = hierarchy_views["Independent", mode]
    units = modules(text)
    assert len(re.findall(r"\s\+\s", units["Independent"])) == 1
    counters = [body for name, body in units.items() if name.startswith("Counter")]
    assert len(counters) == 2
    assert all(len(re.findall(r"\s\+\s", body)) == 1 for body in counters)
    assert all(body.count("always_ff") == 1 for body in counters)


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_reused_wrapper_keeps_its_own_calculation_and_separate_leaf_states(
    hierarchy_views, mode
):
    text, _ = hierarchy_views["Reused", mode]
    units = modules(text)
    wrappers = [body for name, body in units.items() if name.startswith("Biased")]
    counters = [body for name, body in units.items() if name.startswith("Counter")]
    assert len(wrappers) == len(counters) == 2
    assert all(len(re.findall(r"\s\+\s", body)) == 1 for body in wrappers + counters)
    assert all(body.count("always_ff") == 1 for body in counters)
    assert not re.search(r"\s\+\s|always_ff", units["Reused"])


def test_deep_synthesis_retains_source_names_without_anonymous_transport(
    hierarchy_views,
):
    text, _ = hierarchy_views["Deep", "synthesis"]
    assert not re.search(r"\\|\b(?:argument|capture)_\d+\b|__ac_transaction", text)
    assert "count_enable" in text and "amount" in text


def static(value, owner="top", reference=False):
    data = (
        'ref = {kind = "parameter", owner = @'
        + owner
        + ', name = "'
        + str(value)
        + '"}'
        if reference
        else 'value = {kind = "integer", value = #ac.math_int<' + str(value) + ">}"
    )
    return (
        '#ac.static_expr<{kind = "'
        + ("reference" if reference else "literal")
        + '", '
        + data
        + ", origin = {site = {definition = @"
        + owner
        + ', ast_path = []}, expansion = []}, location = {path = "'
        + owner
        + '.py", line = 1 : i64, column = 1 : i64, end_line = 1 : i64, end_column = 2 : i64}}>'
    )


def occurrence(owner, index):
    return (
        "{site = {definition = @"
        + owner
        + ', ast_path = [{kind = "field", name = "body"}, {kind = "index", value = '
        + str(index)
        + " : i64}]}, expansion = []}"
    )


@pytest.fixture(scope="module")
def parameter_views(tmp_path_factory):
    # Explicit final-IR metadata conformance: frontend Method parameterization
    # is a separate admission boundary and is not expanded by this fixture.
    root = tmp_path_factory.mktemp("readable-hierarchy-parameters-native")
    output = {}
    top_path, child_path = occurrence("top", 0), occurrence("middle", 0)
    for width in (5, 13, 130, "collision"):
        parameter = "K" if width == "collision" else "W"
        value_name = "W" if width == "collision" else "value"
        actual_width = 13 if width == "collision" else width
        text = (
            "#root_width = "
            + static(parameter, "top", True)
            + "\n!payload = !ac.bits<#root_width>\n"
        )
        text += "#three = " + static(3) + "\n#one = " + static(1) + "\n"
        text += "module {\n"
        text += '"ac.module"() ({ "ac.yield"() : () -> () }) {sym_name = "leaf", source_owner = {package = "", path = "leaf.py"}, parameters = [{name = "W", type = !ac.math_int}], type_parameters = [], function_type = () -> (), input_names = [], output_names = []} : () -> ()\n'
        text += (
            '"ac.module"() ({\n"ac.instance"() {instance_name = "leaf", callee = @leaf, parameters = [#three], type_arguments = [], occurrence = '
            + child_path
            + "} : () -> ()\n"
        )
        text += '"ac.yield"() : () -> ()\n}) {sym_name = "middle", source_owner = {package = "", path = "middle.py"}, parameters = [{name = "W", type = !ac.math_int}], type_parameters = [], function_type = () -> (), input_names = [], output_names = []} : () -> ()\n'
        text += '"ac.module"() ({\n^bb0(%value: !payload):\n'
        text += (
            '"ac.instance"() {instance_name = "middle", callee = @middle, parameters = [#three], type_arguments = [], occurrence = '
            + top_path
            + "} : () -> ()\n"
        )
        text += '%one = "ac.bits.constant"() {value = #one} : () -> !payload\n'
        text += (
            '%next = "ac.bits.binary"(%value, %one) {opcode = "add"} : (!payload, !payload) -> !payload loc(fused<{ac.rtl_owners = [{root = @top, definition = @leaf, path = ['
            + top_path
            + ", "
            + child_path
            + "]}]}>[unknown])\n"
        )
        text += (
            '"ac.yield"(%next) : (!payload) -> ()\n}) {sym_name = "top", source_owner = {package = "", path = "top.py"}, parameters = [{name = "'
            + parameter
            + '", type = !ac.math_int}], type_parameters = [], function_type = (!payload) -> !payload, input_names = ["'
            + value_name
            + '"], output_names = ["result"]} : () -> ()\n'
        )
        text += (
            '"ac.system"() {entry = {callee = @top, parameters = ['
            + static(actual_width)
            + '], type_arguments = []}, domain = "default"} : () -> ()\n}\n'
        )
        source = root / ("width-" + str(width) + ".mlir")
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
            (root / (str(width) + "-" + mode + ".json")).write_text(json.dumps(data))
            (root / (str(width) + "-" + mode + ".sv")).write_text(rtl)
            output[width, mode] = data, rtl
    return output


@pytest.mark.parametrize("width", [5, 13, 130])
@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_symbolic_owner_width_survives_two_same_named_parameter_scopes(
    parameter_views, width, mode
):
    data, text = parameter_views[width, mode]
    units = modules(text)
    assert not re.search(r"\s\+\s", units["top"])
    assert len(re.findall(r"\s\+\s", units["leaf"])) == 1
    assert "parameter longint signed from_top_W" in units["leaf"]
    assert "[(from_top_W)-1:0]" in units["leaf"]
    assert re.search(r"leaf\s+#\(\s*3\s*,\s*W\s*,\s*from_top_W", units["middle"])
    assert any(
        row.get("receiver_depth") == 2 and row.get("static_parameters") == 2
        for row in data["rtl_value_names"]["ownership_notes"]
    )


def test_generated_transport_port_does_not_capture_a_child_parameter_name(
    parameter_views,
):
    _, text = parameter_views["collision", "synthesis"]
    leaf = modules(text)["leaf"]
    assert "parameter longint signed W" in leaf
    assert "parameter longint signed from_top_K" in leaf
    assert "input wire logic [(from_top_K)-1:0] W_1" in leaf


@pytest.fixture(scope="module")
def type_parameter_views(tmp_path_factory):
    root = tmp_path_factory.mktemp("readable-hierarchy-types-native")
    output = {}
    first, second = occurrence("top", 0), occurrence("middle", 0)
    for case, payload in [("bits", "!b8"), ("record", '!ac.struct<"Packet">')]:
        text = (
            "#w1 = "
            + static(1)
            + "\n#w8 = "
            + static(8)
            + '\n!b1 = !ac.bits<#w1>\n!b8 = !ac.bits<#w8>\n!carrier = !ac.type_param<@top, "T">\nmodule {\n'
        )
        text += 'ac.struct "Packet" fields [{name = "tag", type = !b8}, {name = "payload", type = !b8}]\n'
        text += '"ac.module"() ({ "ac.yield"() : () -> () }) {sym_name = "leaf", source_owner = {package = "", path = "leaf.py"}, parameters = [], type_parameters = ["T"], function_type = () -> (), input_names = [], output_names = []} : () -> ()\n'
        text += (
            '"ac.module"() ({ "ac.instance"() {instance_name = "leaf", callee = @leaf, parameters = [], type_arguments = [!b1], occurrence = '
            + second
            + "} : () -> ()\n"
        )
        text += '"ac.yield"() : () -> () }) {sym_name = "middle", source_owner = {package = "", path = "middle.py"}, parameters = [], type_parameters = ["T"], function_type = () -> (), input_names = [], output_names = []} : () -> ()\n'
        text += '"ac.module"() ({\n^bb0(%base: !carrier, %guard: !b1, %candidate: !carrier):\n'
        text += (
            '"ac.instance"() {instance_name = "middle", callee = @middle, parameters = [], type_arguments = [!b8], occurrence = '
            + first
            + "} : () -> ()\n"
        )
        text += (
            '%next, %enable = "ac.value.merge"(%base, %guard, %candidate) {paths = [[]], operandSegmentSizes = array<i32: 1, 1, 1>} : (!carrier, !b1, !carrier) -> (!carrier, !b1) loc(fused<{ac.rtl_owners = [{root = @top, definition = @leaf, path = ['
            + first
            + ", "
            + second
            + "]}]}>[unknown])\n"
        )
        text += '"ac.yield"(%next) : (!carrier) -> ()\n}) {sym_name = "top", source_owner = {package = "", path = "top.py"}, parameters = [], type_parameters = ["T"], function_type = (!carrier, !b1, !carrier) -> !carrier, input_names = ["base", "guard", "candidate"], output_names = ["result"]} : () -> ()\n'
        text += (
            '"ac.system"() {entry = {callee = @top, parameters = [], type_arguments = ['
            + payload
            + ']}, domain = "default"} : () -> ()\n}\n'
        )
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
            output[case, mode] = data, rtl
    return output


@pytest.mark.parametrize("case", ["bits", "record"])
@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_original_nominal_payload_type_crosses_same_named_type_parameter_scopes(
    type_parameter_views, case, mode
):
    _, text = type_parameter_views[case, mode]
    units = modules(text)
    assert "parameter type from_top_T" in units["leaf"]
    assert "input wire from_top_T base" in units["leaf"]
    assert "input wire from_top_T candidate" in units["leaf"]
    assert "parameter type from_middle_T" in units["leaf"]
    assert "from_top_T" in units["middle"]
    assert "always_ff" not in text


def check_transport(mapping):
    """Reconstruct original hierarchy wire equivalence, independently of cuts."""
    assert mapping["presentation_preserves_common_ir"]
    assert re.fullmatch("[0-9a-f]{64}", mapping["verified_ir_sha256"])
    modules_by_name = {row["rtl_module"]: row for row in mapping["modules"]}
    nodes = {}
    for module in modules_by_name.values():
        for row in module["values"]:
            fields = tuple(
                row[key] if key != "original_operands" else tuple(row[key])
                for key in (
                    "opcode",
                    "source_module",
                    "type",
                    "original_operands",
                    "original_canonical",
                )
            )
            key = row["original_value"]
            assert key not in nodes or nodes[key][1] == fields
            nodes[key] = row, fields
    referenced = {
        row["rtl_callee"]
        for module in modules_by_name.values()
        for row in module["allocations"]
    }
    roots = [name for name in modules_by_name if name not in referenced]
    assert len(roots) == 1, roots
    scopes = []

    def visit(name, parent=None, allocation=None):
        scope = {
            "module": modules_by_name[name],
            "parent": parent,
            "allocation": allocation,
            "index": len(scopes),
        }
        scopes.append(scope)
        for child in scope["module"]["allocations"]:
            if child["rtl_callee"] in modules_by_name:
                visit(child["rtl_callee"], scope, child)
        return scope

    visit(roots[0])

    def residence(value, scope):
        source = nodes[value][0]["source_module"]
        while scope and scope["module"]["source_symbol"] != source:
            scope = scope["parent"]
        assert scope is not None, (value, source)
        return value, scope["index"]

    links = {}

    def find(key):
        links.setdefault(key, key)
        while links[key] != key:
            links[key] = links[links[key]]
            key = links[key]
        return key

    def connect(left, right):
        links[find(left)] = find(right)

    for scope in scopes:
        module = scope["module"]
        for row in module["values"]:
            connect(
                residence(row["original_value"], scope),
                residence(row["original_canonical"], scope),
            )
        if scope["parent"]:
            parent = scope["parent"]
            local = {
                row["optimized_value"]: row["original_value"]
                for row in parent["module"]["values"]
            }
            allocation = scope["allocation"]
            for port, value in zip(
                module["interface"]["inputs"], allocation["inputs"], strict=True
            ):
                connect(
                    residence(port["original_value"], scope),
                    residence(local[value], parent),
                )
            for port, value in zip(
                module["interface"]["outputs"], allocation["outputs"], strict=True
            ):
                connect(
                    residence(port["original_canonical"], scope),
                    residence(local[value], parent),
                )
    counts = {
        "scopes": len(scopes),
        "captures": 0,
        "aliases": 0,
        "replaced_inputs": 0,
        "placements": 0,
        "parameters": 0,
    }
    placements = set()
    for scope in scopes:
        module = scope["module"]
        transport = module["ownership_transport"]
        if not transport:
            continue
        assert scope["parent"]["module"]["rtl_module"] == transport["parent_rtl_module"]
        assert scope["allocation"]["source_name"] == transport["allocation"]
        for port in transport["captures"]:
            if port["local"] is not None:
                original = nodes[port["value"]][0]
                # Original literals may be spelled again in another scope.
                if port["local"] == port["value"] and original["opcode"] in (
                    "ac.bits.constant",
                    "ac.bits.constant4",
                    "ac.enum.create",
                ):
                    continue
                assert find(residence(port["value"], scope)) == find(
                    residence(port["local"], scope)
                )
            else:
                assert port["port"]
        for alias in transport["aliases"]:
            assert find(residence(alias["value"], scope)) == find(
                residence(alias["source"], scope)
            )
        for replacement in transport["replaced_inputs"]:
            original = module["interface"]["inputs"][replacement["input"]][
                "original_value"
            ]
            assert find(residence(original, scope)) == find(
                residence(replacement["source"], scope)
            )
        for results in transport["placements"]:
            key = residence(results[0], scope)
            assert key not in placements
            placements.add(key)
        for key in (
            "captures",
            "aliases",
            "replaced_inputs",
            "placements",
            "parameters",
        ):
            counts[key] += len(transport[key])
    return counts


def test_original_wiring_independently_validates_all_source_scope_cuts(hierarchy_views):
    for _, mapping in hierarchy_views.values():
        assert check_transport(mapping)["placements"] > 0


def test_original_wiring_independently_validates_symbolic_and_type_scope_cuts(
    parameter_views, type_parameter_views
):
    for data, _ in list(parameter_views.values()) + list(type_parameter_views.values()):
        counts = check_transport(data["rtl_value_names"])
        assert counts["placements"] > 0 and counts["parameters"] > 0


def test_transport_checker_rejects_a_different_existing_wire(hierarchy_views):
    _, mapping = hierarchy_views["Deep", "synthesis"]
    broken = deepcopy(mapping)
    counter = next(row for row in broken["modules"] if row["rtl_module"] == "Counter")
    clock = next(
        row["original_value"]
        for row in counter["interface"]["inputs"]
        if row["rtl_port"] == "clk"
    )
    port = next(
        row
        for row in counter["ownership_transport"]["captures"]
        if row["local"] is not None
    )
    port["local"] = clock
    with pytest.raises(AssertionError):
        check_transport(broken)


def test_source_provenance_is_reproducible_across_processes(tmp_path):
    source = tmp_path / "hierarchy.py"
    source.write_text(SOURCE)
    artifacts = []
    for index in range(2):
        unit = tmp_path / f"unit-{index}"
        final = tmp_path / f"design-{index}.ac"
        _ok(
            _cli(
                "compile",
                "-c",
                str(source),
                "--source-root",
                str(tmp_path),
                "--package-prefix",
                "stable_hierarchy",
                "-o",
                str(unit),
            )
        )
        _ok(
            _cli(
                "link",
                str(unit),
                "--top",
                "stable_hierarchy.hierarchy.Reused",
                "-o",
                str(final),
            )
        )
        artifacts.append(final.read_bytes())
    # Include all debug Locations, source bindings and owner overlays.
    assert artifacts[0] == artifacts[1]
