"""Static projection of value availability; no circuit simulation."""

import re

import pytest
from test_source_system_execution import _cli, _ok

SOURCE = """import pycircuit as ac
@ac.struct
class Item:
    valid: ac.u1
    data: ac.u8
@ac.module
def TableCell(index: ac.u1, incoming: Item, store: ac.u1) -> Item:
    entries = ac.table[2, Item](init=0)
    @ac.rule(guard=lambda: store)
    def access() -> Item:
        saved = entries[index]
        if store:
            entries[index] = Item(valid=incoming.valid, data=saved.data + incoming.data)
        return saved
    return access
"""


@pytest.fixture(scope="module")
def sampled_control_views(tmp_path_factory):
    root = tmp_path_factory.mktemp("physical-sampled-controls")
    source = root / "table_cell.py"
    source.write_text(SOURCE)
    unit, final = root / "unit", root / "design.ac"
    _ok(
        _cli(
            "compile",
            "-c",
            str(source),
            "--source-root",
            str(root),
            "--package-prefix",
            "sampled_controls",
            "-o",
            str(unit),
        )
    )
    _ok(
        _cli(
            "link",
            str(unit),
            "--top",
            "sampled_controls.table_cell.TableCell",
            "-o",
            str(final),
        )
    )
    result = {}
    for mode in ("physical", "synthesis"):
        output = root / mode
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
        result[mode] = "\n".join(
            path.read_text() for path in (output / "sources").rglob("*.v")
        )
    return result


def test_physical_sampled_controls_are_checked_at_their_reached_path(
    sampled_control_views,
):
    text = sampled_control_views["physical"]
    assert "admission_error_" in text and "$isunknown(" in text
    assert ".pyc_root_commit_ok(__checks_allow)" in text and "__checks_error" in text


def test_synthesis_keeps_bounds_and_store_control(sampled_control_views):
    text = sampled_control_views["synthesis"]
    assert re.search(r"\(2\)\x27\(\$unsigned\(index\)\) < \(2\)\x27\(2\)", text)
    assert text.count("store") >= 3
    assert not re.search(r"\binitial\b|__checks|pyc_phase", text)
