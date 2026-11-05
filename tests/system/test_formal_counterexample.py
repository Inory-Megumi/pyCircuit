"""Independently check reachable safety search and actual backend replay."""

from __future__ import annotations

import copy
import hashlib
import json
import re
from pathlib import Path

import pytest
import z3
from formal_counterexample import search, write_lean_witness
from formal_counterexample_replay import replay
from test_formal_counter_artifact import _emit, _serialize
from test_formal_rule_export import LEAN_ROOT, ORIGINAL, ExportRun, _sha256
from test_source_system_execution import ROOT

pytestmark = pytest.mark.system


def _export_counter(root: Path, *, faulty: bool):
    harness = ExportRun(root)
    harness.receipt["scope"] = "reachable safety counterexample and backend replay"
    harness.receipt["inputs"][str(Path(__file__).relative_to(ROOT))] = _sha256(
        Path(__file__)
    )
    for name in (
        "formal_counterexample.py",
        "formal_counterexample_replay.py",
        "formal_rule_model.py",
    ):
        helper = Path(__file__).with_name(name)
        harness.receipt["inputs"][str(helper.relative_to(ROOT))] = _sha256(helper)
    z3_module = Path(z3.__file__).resolve()
    harness.receipt["tools"]["z3"] = {
        "version": z3.get_full_version(),
        "python_module": str(z3_module),
        "python_module_sha256": _sha256(z3_module),
        "bundled_libraries": {
            str(path): _sha256(path)
            for path in sorted(z3_module.parent.rglob("libz3*"))
            if path.is_file()
        },
    }
    source = ORIGINAL
    if faulty:
        text = ORIGINAL.read_text()
        before = "count = count + 1"
        assert text.count(before) == 1
        mutation = root / "test-owned-mutation"
        mutation.mkdir()
        source = mutation / ORIGINAL.name
        source.write_text(text.replace(before, "count = count + 2"))
    body = harness.compile(source, "GuardedCounter")
    model, formula = _serialize(harness, body)
    return harness, model, formula


def _read_json(path):
    return json.loads(Path(path).read_text())


def _boolean(op, *arguments):
    return {"op": op, "type": {"kind": "bool"}, "args": list(arguments)}


def _bits(value, width):
    return {
        "op": "bitsLit",
        "type": {"kind": "bits", "width": width},
        "value": str(value),
    }


def _specification():
    count = {"op": "read", "type": {"kind": "bits", "width": 3}, "index": 0}
    active_requests = [
        _boolean(
            "eq",
            {"op": "input", "type": {"kind": "bits", "width": 1}, "index": index},
            _bits(1, 1),
        )
        for index in (0, 1)
    ]
    return {
        "schema": "pycircuit-rule-property-v1",
        "name": "count_at_most_capacity_five",
        "property": _boolean("not", _boolean("ult", _bits(5, 3), count)),
        "environment": _boolean("not", _boolean("and", *active_requests)),
    }


@pytest.fixture(scope="module")
def healthy_counter(tmp_path_factory):
    harness, model, formula = _export_counter(
        tmp_path_factory.mktemp("reachable-healthy"), faulty=False
    )
    try:
        yield harness, model, formula
    finally:
        harness.finish()


@pytest.fixture(scope="module")
def faulty_counter(tmp_path_factory):
    harness, model, formula = _export_counter(
        tmp_path_factory.mktemp("reachable-faulty"), faulty=True
    )
    try:
        specification = _specification()
        case = search(formula, specification, max_depth=6)
        assert specification == _specification()
        case["source_sha256"] = _sha256(harness.root / "source" / ORIGINAL.name)
        case["model_sha256"] = _sha256(model)
        (harness.root / "counterexample.json").write_text(
            json.dumps(case, indent=2) + "\n"
        )
        yield harness, model, formula, case
    finally:
        harness.finish()


def test_healthy_counter_has_no_reachable_violation_through_bound(healthy_counter):
    harness, _, formula = healthy_counter
    specification = _specification()
    result = search(formula, specification, max_depth=6)
    assert specification == _specification()
    assert result["status"] == "bounded_unsat"
    assert result["initialization"] == "declared"
    assert result["bound"] == 6
    assert [(row["depth"], row["status"]) for row in result["depths"]] == [
        (depth, "unsat") for depth in range(7)
    ]
    assert "rows" not in result
    (harness.root / "bounded-search.json").write_text(
        json.dumps(result, indent=2) + "\n"
    )
    harness.receipt["bounded_search"] = result
    harness.receipt["status"] = "passed"


def _vcd_known_changes(path, signal):
    lines = Path(path).read_text().splitlines()
    identifiers = {
        fields[3]
        for line in lines
        if (fields := line.split()) and fields[0] == "$var" and fields[4] == signal
    }
    assert len(identifiers) == 1, (signal, identifiers)
    identifier = identifiers.pop()
    changes = []
    for line in lines:
        fields = line.split()
        if len(fields) != 2 or fields[1] != identifier or not fields[0].startswith("b"):
            continue
        digits = fields[0][1:]
        if set(digits) <= {"0", "1"}:
            value = int(digits, 2)
            if not changes or changes[-1] != value:
                changes.append(value)
    return changes


def test_discovered_shortest_violation_is_kernel_checked_and_replayed(faulty_counter):
    harness, model, formula, case = faulty_counter
    assert case["status"] == "counterexample"
    assert case["initialization"] == "declared"
    assert case["formula_sha256"] == _sha256(formula)
    assert case["specification"] == _specification()
    assert (
        case["specification_sha256"]
        == hashlib.sha256(
            json.dumps(_specification(), sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest()
    )
    assert case["violation_depth"] == 3
    assert case["shortest"] is True
    assert [(row["depth"], row["status"]) for row in case["depths"]] == [
        (0, "unsat"),
        (1, "unsat"),
        (2, "unsat"),
        (3, "sat"),
    ]
    expected_rows = [
        {"inputs": [1, 0], "state": [0], "outputs": [0]},
        {"inputs": [1, 0], "state": [2], "outputs": [2]},
        {"inputs": [1, 0], "state": [4], "outputs": [4]},
        {"inputs": [0, 0], "state": [6], "outputs": [6]},
    ]
    assert case["rows"] == expected_rows
    frozen = {"source": _sha256(harness.root / "source" / ORIGINAL.name)}
    frozen.update({"model": _sha256(model), "formula": _sha256(formula)})
    obligation = write_lean_witness(model, formula, case, harness.root / "Witness.lean")
    checked = harness.run(
        "kernel-witness",
        [*harness.lean, "-DwarningAsError=true", str(obligation)],
        cwd=LEAN_ROOT,
    )
    transcript = checked.stdout + checked.stderr
    assert "sorryAx" not in transcript
    audits = re.findall(r"depends on axioms:\s*\[([^]]*)\]", transcript)
    assert len(audits) >= 2
    for dependencies in audits:
        assert {name.strip() for name in dependencies.split(",") if name.strip()} <= {
            "propext",
            "Quot.sound",
            "Classical.choice",
        }
    rtl = _emit(harness, cpp=True)
    observed = replay(
        case, formula, harness.root / "cpp", rtl, harness.run, harness.root / "replay"
    )
    assert observed["rows"] == len(expected_rows)
    assert _read_json(observed["cpp_trace"]) == expected_rows
    assert _read_json(observed["rtl_trace"]) == expected_rows
    for signal in ("r0", "o0"):
        assert _vcd_known_changes(observed["vcd"], signal) == [0, 2, 4, 6]
    assert frozen == {
        "source": _sha256(harness.root / "source" / ORIGINAL.name),
        "model": _sha256(model),
        "formula": _sha256(formula),
    }
    harness.receipt["counterexample"] = case
    harness.receipt["replay"] = {key: str(value) for key, value in observed.items()}
    harness.receipt["frozen_dut"] = frozen
    harness.receipt["status"] = "passed"


def test_environment_constrains_transitions_but_not_final_observation(faulty_counter):
    harness, model, formula, original = faulty_counter
    specification = _specification()
    specification["name"] = "increment_forbidden_on_transitions"
    specification["environment"] = _boolean(
        "eq",
        {"op": "input", "type": {"kind": "bits", "width": 1}, "index": 0},
        _bits(0, 1),
    )
    blocked = search(formula, specification, max_depth=6)
    assert blocked["status"] == "bounded_unsat"
    assert [(row["depth"], row["status"]) for row in blocked["depths"]] == [
        (depth, "unsat") for depth in range(7)
    ]
    assert "rows" not in blocked
    (harness.root / "environment-blocked-search.json").write_text(
        json.dumps(blocked, indent=2) + "\n"
    )
    specification["name"] = "increment_required_on_transitions"
    specification["environment"] = _boolean(
        "eq",
        {"op": "input", "type": {"kind": "bits", "width": 1}, "index": 0},
        _bits(1, 1),
    )
    case = search(formula, specification, max_depth=6)
    case["source_sha256"] = original["source_sha256"]
    case["model_sha256"] = original["model_sha256"]
    assert case["status"] == "counterexample"
    assert case["violation_depth"] == 3
    assert case["shortest"] is True
    assert [row["state"] for row in case["rows"]] == [[0], [2], [4], [6]]
    assert all(row["inputs"][0] == 1 for row in case["rows"][:-1])
    assert case["rows"][-1]["inputs"] == [0, 0]
    (harness.root / "phase-counterexample.json").write_text(
        json.dumps(case, indent=2) + "\n"
    )
    obligation = write_lean_witness(
        model, formula, case, harness.root / "PhaseWitness.lean"
    )
    checked = harness.run(
        "kernel-final-observation-phase",
        [*harness.lean, "-DwarningAsError=true", str(obligation)],
        cwd=LEAN_ROOT,
    )
    transcript = checked.stdout + checked.stderr
    assert "sorryAx" not in transcript
    audits = re.findall(r"depends on axioms:\s*\[([^]]*)\]", transcript)
    assert len(audits) >= 2
    for dependencies in audits:
        assert {name.strip() for name in dependencies.split(",") if name.strip()} <= {
            "propext",
            "Quot.sound",
            "Classical.choice",
        }
    harness.receipt["final_observation_phase"] = case
    harness.receipt["environment_blocked_search"] = blocked


@pytest.mark.parametrize("field", ["state", "inputs", "outputs"])
def test_altered_solver_witness_is_rejected_by_lean(faulty_counter, field):
    harness, model, formula, case = faulty_counter
    altered = copy.deepcopy(case)
    if field == "inputs":
        altered["rows"][0][field][0] = 0
    else:
        altered["rows"][1][field][0] = 3
    obligation = write_lean_witness(
        model, formula, altered, harness.root / f"Invalid-{field}.lean"
    )
    rejected = harness.run(
        f"kernel-reject-{field}",
        [*harness.lean, "-DwarningAsError=true", str(obligation)],
        cwd=LEAN_ROOT,
        failure=True,
    )
    assert rejected.returncode != 0
    diagnostic = rejected.stdout + rejected.stderr
    assert "decide" in diagnostic and "false" in diagnostic


def test_unknown_stops_search_without_a_counterexample(healthy_counter):
    harness, _, formula = healthy_counter

    class UnknownSolver(z3.Solver):
        def check(self, *assumptions):
            return z3.unknown

        def reason_unknown(self):
            return "independent acceptance interruption"

    result = search(
        formula, _specification(), max_depth=6, solver_factory=UnknownSolver
    )
    assert result["status"] == "unknown"
    assert len(result["depths"]) == 1
    assert result["depths"][0]["depth"] == 0
    assert result["depths"][0]["status"] == "unknown"
    assert result["depths"][0]["reason"] == "independent acceptance interruption"
    assert "rows" not in result
    assert not result.get("shortest", False)
    harness.receipt["unknown_search"] = result
