"""Static source-to-RTL checks; these tests never invoke a simulator."""

import json
import re

from test_physical_rtl_readability import design_text
from test_physical_rtl_readability import readable_designs as _readable_designs

readable_designs = _readable_designs


def test_shared_source_binding_names_one_actual_wire(readable_designs):
    output = readable_designs["Fanout"]
    text = design_text(output)
    assert len(re.findall(r"\s\+\s", text)) == 1
    assert re.search(r"\bshared\b", text)
    mapping = json.loads((output / "rtl-names.json").read_text())
    assert mapping["schema"] == "pycircuit-rtl-value-names/v1"
    bindings = [
        row
        for row in mapping["bindings"]
        if row["source_name"] == "shared" and row["module"] == "Fanout"
    ]
    assert bindings
    assert {row["rtl_expression"] for row in bindings} == {"shared"}


def test_named_narrow_value_remains_narrow_before_widening(readable_designs):
    text = design_text(readable_designs["Widened"])
    assert re.search(r"logic \[3:0\] narrow;", text)
    assert re.search(r"logic \[7:0\] wide;", text)
    assert re.search(r"assign narrow = .*\+.*;", text)
    assert re.search(r"assign wide = .*narrow.*;", text)
    assert len(re.findall(r"\s\+\s", text)) == 1


def test_no_anonymous_net_names_replace_retained_bindings(readable_designs):
    for name in ("Fanout", "Narrow", "Widened", "Slice"):
        assert "pyc_net_" not in design_text(readable_designs[name])
