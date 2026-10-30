"""Source names and transaction roles; native compile/emit only."""

import json
import re

import pytest
from test_source_system_execution import _cli, _ok

SOURCE = """import pycircuit as ac
@ac.struct
class Cell:
    present: ac.u1
    data: ac.u8
@ac.module
def Sequence(first: ac.u2, second: ac.u2, incoming: ac.u8, insert: ac.u1, remove: ac.u1) -> Cell:
    entries = ac.table[4, Cell](init=0)
    @ac.method
    def receive() -> None:
        if insert:
            entries[first] = Cell(present=1, data=incoming)
    @ac.method
    def release() -> Cell:
        result = entries[second]
        if remove:
            entries[second] = Cell()
        return result
    @ac.rule
    def transact() -> Cell:
        receive()
        observed = release()
        return observed
    return transact
@ac.module
def Shared(first: ac.u8, second: ac.u8) -> tuple[ac.u8, ac.u8]:
    left: ac.u8 = 0
    right: ac.u8 = 0
    condition = first + second != 0
    @ac.method
    def alpha() -> None:
        if condition:
            left = first
    @ac.method
    def beta() -> None:
        if condition:
            right = second
    @ac.rule
    def transact() -> None:
        alpha()
        beta()
    return left, right
@ac.module
def Aliases(first: ac.u8, second: ac.u8) -> tuple[ac.u8, ac.u8]:
    total = first + second
    @ac.method
    def alpha() -> ac.u8:
        return total
    @ac.method
    def beta() -> ac.u8:
        return total
    @ac.rule
    def compute() -> tuple[ac.u8, ac.u8]:
        left = alpha()
        right = beta()
        return left, right
    return compute
"""

SOURCE += (
    SOURCE[
        SOURCE.index("@ac.module\ndef Sequence") : SOURCE.index(
            "@ac.module\ndef Shared"
        )
    ]
    .replace("def Sequence(", "def Renamed(")
    .replace("receive", "accept_word")
    .replace("release", "drop_word")
)
ROOTS = ("Sequence", "Shared", "Aliases", "Renamed")


@pytest.fixture(scope="module")
def role_views(tmp_path_factory):
    root = tmp_path_factory.mktemp("readable-source-roles")
    source = root / "roles.py"
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
            "readable_roles",
            "-o",
            str(unit),
        )
    )
    views = {}
    for name in ROOTS:
        final = root / (name + ".ac")
        _ok(
            _cli(
                "link",
                str(unit),
                "--top",
                "readable_roles.roles." + name,
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
            views[name, mode] = text, json.loads(
                (output / "rtl-names.json").read_text()
            )
    return views


def roles(mapping):
    return [
        role
        for module in mapping["modules"]
        for value in module["values"]
        for role in value.get("source_roles", [])
    ]


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
@pytest.mark.parametrize(
    "name,receive,release",
    [("Sequence", "receive", "release"), ("Renamed", "accept_word", "drop_word")],
)
def test_source_method_and_state_names_define_roles(
    role_views, mode, name, receive, release
):
    text, mapping = role_views[name, mode]
    assert receive + "_entries_hit" in text and release + "_entries_hit" in text
    assert "entries_after_" + receive in text
    assert "observed" in text
    flow = next(role for role in roles(mapping) if role["role"] == "flow")
    assert [(call["caller"], call["callee"]) for call in flow["calls"]] == [
        ("transact", receive),
        ("transact", release),
    ]
    assert all(
        call["versions"] and call["versions"][0]["state"] == "entries"
        for call in flow["calls"]
    )
    assert "complete_condition" not in text and "allocate_condition" not in text


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_storage_write_enable_is_the_original_endpoint_with_a_role_name(
    role_views, mode
):
    text, _ = role_views["Sequence", mode]
    if mode == "synthesis":
        assert (
            "entries_write_enable" in text and "else if (entries_write_enable)" in text
        )
        assert text.count("always_ff") == 1 and text.count("for (genvar") == 2
    else:
        assert ".pyc_root_commit_ok(__checks_allow)" in text
    assert "=== 1'b1" in text or "insert ?" in text or "remove ?" in text


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_cse_keeps_both_condition_origins_without_repeating_arithmetic(
    role_views, mode
):
    text, mapping = role_views["Shared", mode]
    assert len(re.findall(r"\s\+\s", text)) == 1
    shared = [
        value
        for module in mapping["modules"]
        for value in module["values"]
        if {
            role["scope"]
            for role in value.get("source_roles", [])
            if role["role"] == "condition"
        }
        == {"alpha", "beta"}
    ]
    assert shared and "condition" in text
    assert text.count("always_ff") == 2


@pytest.mark.parametrize("mode", ["physical", "synthesis"])
def test_shared_caller_aliases_retain_original_bindings(role_views, mode):
    text, mapping = role_views["Aliases", mode]
    assert len(re.findall(r"\s\+\s", text)) == 1
    bindings = {binding["source_name"] for binding in mapping["bindings"]}
    assert {"total", "left", "right"} <= bindings
    assert "left" in text and "right" in text
