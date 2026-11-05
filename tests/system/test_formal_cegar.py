"""Check actual bounded abstraction, refinement certificates, and replay."""

from __future__ import annotations

import copy
import json
import re
from pathlib import Path

import pytest
import z3
from formal_cegar import search_cegar
from formal_cegar_certificate import write_lean_refinement
from formal_counterexample import write_lean_witness
from formal_counterexample_replay import replay
from test_formal_counter_artifact import _emit
from test_formal_counterexample import (
    _read_json,
    _specification,
    _vcd_known_changes,
)
from test_formal_counterexample import (
    faulty_counter as _faulty_counter_fixture,
)
from test_formal_counterexample import (
    healthy_counter as _healthy_counter_fixture,
)
from test_formal_rule_export import LEAN_ROOT, ORIGINAL, _sha256
from test_source_system_execution import ROOT

pytestmark = pytest.mark.system
healthy_counter = _healthy_counter_fixture
faulty_counter = _faulty_counter_fixture


def _record_inputs(harness):
    harness.receipt["scope"] = "bounded CEGAR with kernel refinement and backend replay"
    for path in (
        Path(__file__),
        Path(__file__).with_name("formal_cegar.py"),
        Path(__file__).with_name("formal_cegar_certificate.py"),
        Path(__file__).with_name("test_formal_counter_artifact.py"),
    ):
        harness.receipt["inputs"][str(path.relative_to(ROOT))] = _sha256(path)


def _run_cegar(harness, model, formula):
    _record_inputs(harness)
    paths = {
        "source": harness.root / "source" / ORIGINAL.name,
        "model": model,
        "formula": formula,
    }
    frozen = {name: _sha256(path) for name, path in paths.items()}
    specification = _specification()
    result = search_cegar(formula, specification, max_depth=6)
    assert specification == _specification()
    assert {name: _sha256(path) for name, path in paths.items()} == frozen
    cases = [iteration["search"] for iteration in result["iterations"]]
    if "counterexample" in result:
        cases.append(result["counterexample"])
    for case in cases:
        case["source_sha256"] = frozen["source"]
        case["model_sha256"] = frozen["model"]
    (harness.root / "cegar-result.json").write_text(json.dumps(result, indent=2) + "\n")
    harness.receipt["cegar_result"] = result
    harness.receipt["cegar_frozen_dut"] = frozen
    return result


@pytest.fixture(scope="module")
def healthy_cegar(healthy_counter):
    harness, model, formula = healthy_counter
    return harness, model, formula, _run_cegar(harness, model, formula)


@pytest.fixture(scope="module")
def faulty_cegar(faulty_counter):
    harness, model, formula, baseline = faulty_counter
    return harness, model, formula, _run_cegar(harness, model, formula), baseline


def _check_lean(harness, label, obligation):
    checked = harness.run(
        label,
        [*harness.lean, "-DwarningAsError=true", str(obligation)],
        cwd=LEAN_ROOT,
    )
    transcript = checked.stdout + checked.stderr
    assert "sorryAx" not in transcript
    audits = re.findall(r"depends on axioms:\s*\[([^]]*)\]", transcript)
    assert len(audits) >= 2
    for audit in audits:
        assert {name.strip() for name in audit.split(",") if name.strip()} <= {
            "propext",
            "Quot.sound",
            "Classical.choice",
        }


def _check_spurious_then_refined(harness, model, formula, result):
    assert result["schema"] == "pycircuit-rule-cegar-v1"
    assert result["bound"] == 6
    assert result["retained_registers"] == [0]
    assert len(result["iterations"]) == 2
    first, final = result["iterations"]
    assert first["retained_registers"] == []
    abstract = first["search"]
    assert abstract["status"] == "abstract_counterexample"
    assert abstract["violation_depth"] == 1
    assert abstract["rows"][0]["state"] == [0]
    assert abstract["rows"][-1]["state"][0] in (6, 7)
    assert first["concretization"]["status"] == "unsat"
    assert first["refinement"]["register"] == 0
    assert first["refinement"]["edge"] == 0
    assert first["refinement"]["retained_registers"] == [0]
    assert final["retained_registers"] == [0]
    obligation = write_lean_refinement(
        model, formula, first, harness.root / "Refinement.lean"
    )
    _check_lean(harness, "kernel-cegar-refinement", obligation)


def test_healthy_counter_refines_spurious_trace_then_is_bounded_safe(healthy_cegar):
    harness, model, formula, result = healthy_cegar
    _check_spurious_then_refined(harness, model, formula, result)
    assert result["status"] == "bounded_unsat"
    final = result["iterations"][-1]["search"]
    assert final["status"] == "bounded_unsat"
    assert [(row["depth"], row["status"]) for row in final["depths"]] == [
        (depth, "unsat") for depth in range(7)
    ]
    assert "counterexample" not in result
    harness.receipt["status"] = "passed"


def test_faulty_counter_refines_then_replays_real_shortest_trace(faulty_cegar):
    harness, model, formula, result, baseline = faulty_cegar
    _check_spurious_then_refined(harness, model, formula, result)
    assert result["status"] == "counterexample"
    assert result["iterations"][-1]["concretization"]["status"] == "sat"
    case = result["counterexample"]
    assert case["violation_depth"] == 3 and case["shortest"] is True
    assert [(row["depth"], row["status"]) for row in case["depths"]] == [
        (0, "unsat"),
        (1, "unsat"),
        (2, "unsat"),
        (3, "sat"),
    ]
    expected = [
        {"inputs": [1, 0], "state": [0], "outputs": [0]},
        {"inputs": [1, 0], "state": [2], "outputs": [2]},
        {"inputs": [1, 0], "state": [4], "outputs": [4]},
        {"inputs": [0, 0], "state": [6], "outputs": [6]},
    ]
    assert case["rows"] == baseline["rows"] == expected
    (harness.root / "cegar-counterexample.json").write_text(
        json.dumps(case, indent=2) + "\n"
    )
    obligation = write_lean_witness(
        model, formula, case, harness.root / "CegarWitness.lean"
    )
    _check_lean(harness, "kernel-cegar-witness", obligation)
    rtl = _emit(harness, cpp=True)
    observed = replay(
        case, formula, harness.root / "cpp", rtl, harness.run, harness.root / "replay"
    )
    assert observed["rows"] == 4
    assert _read_json(observed["cpp_trace"]) == expected
    assert _read_json(observed["rtl_trace"]) == expected
    for signal in ("r0", "o0"):
        assert _vcd_known_changes(observed["vcd"], signal) == [0, 2, 4, 6]
    harness.receipt["cegar_replay"] = {
        key: str(value) if isinstance(value, Path) else value
        for key, value in observed.items()
    }
    harness.receipt["status"] = "passed"


def test_budget_exhaustion_reports_incomplete_results(healthy_counter):
    harness, _, formula = healthy_counter
    _record_inputs(harness)
    limited = search_cegar(formula, _specification(), max_depth=6, max_refinements=0)
    assert limited["status"] == "refinement_limit"
    assert limited["retained_registers"] == []
    assert len(limited["iterations"]) == 1
    first = limited["iterations"][0]
    assert first["search"]["status"] == "abstract_counterexample"
    assert first["search"]["violation_depth"] == 1
    assert first["concretization"]["status"] == "unsat"
    assert "refinement" not in first
    assert "counterexample" not in limited

    class NoCheckSolver(z3.Solver):
        def check(self, *assumptions):
            pytest.fail("zero solver budget must stop before a check")

    exhausted = search_cegar(
        formula,
        _specification(),
        max_depth=6,
        max_solver_calls=0,
        solver_factory=NoCheckSolver,
    )
    assert exhausted["status"] == "resource_limit"
    assert exhausted["retained_registers"] == []
    assert "counterexample" not in exhausted
    assert all("refinement" not in row for row in exhausted["iterations"])
    partial = search_cegar(formula, _specification(), max_depth=6, max_solver_calls=1)
    assert partial["status"] == "resource_limit"
    assert partial["resources"]["solver_calls"] == 1
    assert partial["retained_registers"] == []
    assert "counterexample" not in partial
    assert len(partial["iterations"]) == 1
    search = partial["iterations"][0]["search"]
    assert search["status"] == "resource_limit"
    assert search["depths"] == [{"depth": 0, "status": "unsat"}]
    assert "rows" not in search
    assert "refinement" not in partial["iterations"][0]
    harness.receipt["cegar_budget_controls"] = {
        "refinement_limit": limited,
        "resource_limit": exhausted,
        "partial_search": partial,
    }


@pytest.mark.parametrize("stage,unknown_call", [("abstract", 1), ("concretization", 2)])
def test_unknown_at_either_solver_stage_stops_without_refinement(
    healthy_counter, stage, unknown_call
):
    harness, _, formula = healthy_counter
    _record_inputs(harness)
    calls = 0

    class UnknownSolver(z3.Solver):
        def check(self, *assumptions):
            return z3.unknown

        def reason_unknown(self):
            return "independent CEGAR acceptance interruption"

    def solver_factory():
        nonlocal calls
        calls += 1
        return UnknownSolver() if calls == unknown_call else z3.Solver()

    result = search_cegar(
        formula, _specification(), max_depth=6, solver_factory=solver_factory
    )
    assert result["status"] == "unknown"
    assert calls == unknown_call
    assert result["retained_registers"] == []
    assert "counterexample" not in result
    assert len(result["iterations"]) == 1
    iteration = result["iterations"][0]
    assert "refinement" not in iteration
    if stage == "abstract":
        assert iteration["search"]["status"] == "unknown"
    else:
        assert iteration["search"]["status"] == "abstract_counterexample"
        assert iteration["concretization"]["status"] == "unknown"
    harness.receipt.setdefault("cegar_unknown_controls", {})[stage] = result


def test_lean_rejects_refinement_that_keeps_havoc_relation(healthy_cegar):
    harness, model, formula, result = healthy_cegar
    altered = copy.deepcopy(result["iterations"][0])
    altered["refinement"]["retained_registers"] = []
    obligation = write_lean_refinement(
        model, formula, altered, harness.root / "InvalidRefinement.lean"
    )
    rejected = harness.run(
        "kernel-reject-cegar-refinement",
        [*harness.lean, "-DwarningAsError=true", str(obligation)],
        cwd=LEAN_ROOT,
        failure=True,
    )
    assert rejected.returncode != 0
    transcript = rejected.stdout + rejected.stderr
    assert "decide" in transcript and "false" in transcript
