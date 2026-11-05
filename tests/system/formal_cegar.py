"""Bounded CEGAR by restoring omitted register transition equations."""

from __future__ import annotations

import copy

import z3
from formal_counterexample import (
    _encode,
    _json_hash,
    _search,
    _SearchLimitError,
    _specification,
)
from formal_rule_model import RuleFormula, _natural, _require


class _Budget:
    def __init__(self, max_solver_calls, max_work):
        self.max_solver_calls, self.max_work = max_solver_calls, max_work
        self.solver_calls = self.work = 0

    def check(self, solver, work):
        if self.solver_calls >= self.max_solver_calls:
            raise _SearchLimitError("aggregate solver call budget exhausted")
        if self.work + work > self.max_work:
            raise _SearchLimitError("aggregate formula work budget exhausted")
        self.solver_calls += 1
        self.work += work
        return solver.check()

    def receipt(self):
        return {
            "max_solver_calls": self.max_solver_calls,
            "solver_calls": self.solver_calls,
            "max_work": self.max_work,
            "charged_work": self.work,
            "work_basis": "validated term-bit work times queried path rows",
        }


def _concretize(formula, candidate, timeout_ms, solver_factory, budget, work):
    """Bind every advertised row, not merely a satisfiable input sequence."""
    solver = solver_factory()
    solver.set(timeout=timeout_ms)
    states, inputs = [], []
    for row in candidate["rows"]:
        states.append(
            [
                z3.BitVecVal(value, width)
                for value, width in zip(row["state"], formula.widths, strict=True)
            ]
        )
        inputs.append(
            [
                (
                    z3.BoolVal(bool(value))
                    if kind == "bool"
                    else z3.BitVecVal(value, width)
                )
                for value, (kind, width) in zip(
                    row["inputs"], formula.input_types, strict=True
                )
            ]
        )
    solver.add(
        *[
            value == initial
            for value, initial in zip(states[0], formula.initials, strict=True)
        ]
    )
    violated = []
    for edge, (row, state, incoming) in enumerate(
        zip(candidate["rows"], states, inputs, strict=True)
    ):
        solver.add(
            *[
                _encode(formula, output["term"], state, incoming) == value
                for output, value in zip(formula.outputs, row["outputs"], strict=True)
            ]
        )
        if edge + 1 == len(states):
            solver.add(
                z3.Not(
                    _encode(
                        formula, candidate["specification"]["property"], state, incoming
                    )
                )
            )
            continue
        solver.add(
            _encode(formula, candidate["specification"]["environment"], state, incoming)
        )
        for register, term in enumerate(formula.data["next"]):
            equation = states[edge + 1][register] == _encode(
                formula, term, state, incoming
            )
            solver.add(equation)
            if z3.is_false(z3.simplify(equation)):
                violated.append({"edge": edge, "register": register})
    answer = budget.check(solver, work * len(states))
    outcome = {"status": str(answer)}
    if answer == z3.unknown:
        outcome["reason"] = solver.reason_unknown()
    else:
        _require(answer in (z3.sat, z3.unsat), "unexpected concretization result")
    return outcome, violated


def search_cegar(
    formula_path,
    specification,
    *,
    max_depth=6,
    timeout_ms=10000,
    retained_registers=(),
    max_refinements=None,
    max_solver_calls=256,
    max_work=16000000,
    solver_factory=None,
):
    """Refine a finite equation abstraction; only feasible cases become concrete.

    Search results remain solver-backed. Refinement certificates and actual backend
    replay are explicit subsequent operations, just as with concrete search.
    """
    formula = RuleFormula.load(formula_path)
    specification = copy.deepcopy(specification)
    work = _specification(formula, specification)
    _require(_natural(max_depth) and max_depth <= 64, "search depth outside profile")
    _require(_natural(timeout_ms) and 0 < timeout_ms <= 60000, "invalid solver timeout")
    _require(work * (max_depth + 1) <= 16000000, "unrolled formula work limit exceeded")
    _require(
        isinstance(retained_registers, list | tuple)
        and all(
            _natural(index) and index < len(formula.registers)
            for index in retained_registers
        )
        and len(set(retained_registers)) == len(retained_registers),
        "invalid retained register inventory",
    )
    retained = sorted(retained_registers)
    available = len(formula.registers) - len(retained)
    if max_refinements is None:
        max_refinements = available
    _require(
        _natural(max_refinements) and max_refinements <= available,
        "refinement limit exceeds omitted register count",
    )
    _require(
        _natural(max_solver_calls) and max_solver_calls <= 256,
        "solver call budget outside profile",
    )
    _require(_natural(max_work) and max_work <= 16000000, "work budget outside profile")
    budget = _Budget(max_solver_calls, max_work)
    solver_factory = solver_factory or z3.Solver
    result = {
        "schema": "pycircuit-rule-cegar-v1",
        "formula_sha256": formula.sha256,
        "definition": formula.definition,
        "specification": specification,
        "specification_sha256": _json_hash(specification),
        "initialization": "declared",
        "solver": {
            "name": "z3",
            "version": z3.get_full_version(),
            "timeout_ms": timeout_ms,
        },
        "bound": max_depth,
        "initial_retained_registers": list(retained),
        "max_refinements": max_refinements,
        "iterations": [],
    }

    def finish(status, **fields):
        result.update(
            status=status,
            retained_registers=list(retained),
            resources=budget.receipt(),
            **fields,
        )
        return result

    for refinement_count in range(max_refinements + 1):
        iteration = {"retained_registers": list(retained)}
        result["iterations"].append(iteration)
        stage = "abstract_search"
        try:
            abstract = _search(
                formula,
                specification,
                max_depth=max_depth,
                timeout_ms=timeout_ms,
                solver_factory=solver_factory,
                retained_registers=retained,
                check_solver=lambda solver, depth: budget.check(
                    solver, work * (depth + 1)
                ),
            )
            iteration["search"] = abstract
            if abstract["status"] == "resource_limit":
                iteration["interrupted"] = {
                    "stage": stage,
                    "reason": abstract["reason"],
                }
                return finish("resource_limit", stage=stage, reason=abstract["reason"])
            if abstract["status"] == "unknown":
                return finish("unknown", stage=stage)
            if abstract["status"] == "bounded_unsat":
                return finish("bounded_unsat")
            _require(
                abstract["status"] == "abstract_counterexample",
                "unexpected abstract search status",
            )
            stage = "concretization"
            concrete, violated = _concretize(
                formula, abstract, timeout_ms, solver_factory, budget, work
            )
            iteration["concretization"] = concrete
            if concrete["status"] == "unknown":
                return finish("unknown", stage=stage)
            if concrete["status"] == "sat":
                case = copy.deepcopy(abstract)
                case.update(
                    schema="pycircuit-rule-counterexample-v1",
                    status="counterexample",
                    search_basis={
                        "kind": "equation_abstraction",
                        "retained_registers": case.pop("retained_registers"),
                        "shortest_basis": "abstract UNSAT prefix and concrete SAT path",
                    },
                )
                return finish("counterexample", counterexample=case)
            _require(
                violated and all(item["register"] not in retained for item in violated),
                "concretization discrepancy is not an omitted update equation",
            )
            if refinement_count == max_refinements:
                return finish("refinement_limit", stage="refinement")
            selected = violated[0]
            retained = sorted([*retained, selected["register"]])
            iteration["refinement"] = {
                **selected,
                "retained_registers": list(retained),
            }
        except _SearchLimitError as error:
            iteration["interrupted"] = {"stage": stage, "reason": str(error)}
            return finish("resource_limit", stage=stage, reason=str(error))
    raise AssertionError("refinement loop must terminate with a recorded outcome")
