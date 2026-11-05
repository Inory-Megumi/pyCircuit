"""Reachable finite-width safety search and concrete Lean witness generation."""

from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path

import z3
from formal_rule_model import RuleFormula, _natural, _require


class _SearchLimitError(Exception):
    """A caller's aggregate resource budget interrupted a solver query."""


def _json_hash(value):
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def _specification(formula, specification):
    _require(
        isinstance(specification, dict)
        and set(specification) == {"schema", "name", "property", "environment"}
        and specification["schema"] == "pycircuit-rule-property-v1"
        and isinstance(specification["name"], str)
        and bool(specification["name"]),
        "unsupported property specification",
    )
    budget = [formula.term_visits, formula.bit_work]
    for name in ("property", "environment"):
        type_, _ = formula.fold(
            specification[name], allow_inputs=name != "property", budget=budget
        )
        _require(type_ == ("bool", 1), "property/environment must be Bool")
    return budget[1]


def _encode(formula, node, state, inputs):
    def render(node, type_, children):
        op = node["op"]
        if op == "read":
            return state[node["index"]]
        if op == "input":
            return inputs[node["index"]]
        if op == "boolLit":
            return z3.BoolVal(node["value"])
        if op == "bitsLit":
            return z3.BitVecVal(int(node["value"]), type_[1])
        if op == "add":
            return children[0] + children[1]
        if op == "sub":
            return children[0] - children[1]
        if op == "ult":
            return z3.ULT(*children)
        if op == "eq":
            return children[0] == children[1]
        if op == "and":
            return z3.And(*children)
        if op == "not":
            return z3.Not(children[0])
        if op == "ite":
            return z3.If(*children)
        if op == "bit":
            return z3.If(children[0], z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))
        if op == "concat":
            return z3.Concat(*children)
        raise AssertionError("unvalidated expression")

    return formula.fold(node, render)[1]


def _zero_inputs(formula):
    return [
        z3.BoolVal(False) if kind == "bool" else z3.BitVecVal(0, width)
        for kind, width in formula.input_types
    ]


def search(
    formula_path, specification, *, max_depth=6, timeout_ms=10000, solver_factory=None
):
    """Search increasing reachable depths; UNSAT is bounded, UNKNOWN stops."""
    formula = RuleFormula.load(formula_path)
    return _search(
        formula,
        specification,
        max_depth=max_depth,
        timeout_ms=timeout_ms,
        solver_factory=solver_factory,
    )


def _search(
    formula,
    specification,
    *,
    max_depth,
    timeout_ms,
    solver_factory=None,
    retained_registers=None,
    check_solver=None,
):
    """Shared bounded engine; omitted update equations are explicitly abstract."""
    specification = copy.deepcopy(specification)
    work = _specification(formula, specification)
    _require(_natural(max_depth) and max_depth <= 64, "search depth outside profile")
    _require(_natural(timeout_ms) and 0 < timeout_ms <= 60000, "invalid solver timeout")
    _require(work * (max_depth + 1) <= 16000000, "unrolled formula work limit exceeded")
    result = {
        "schema": "pycircuit-rule-counterexample-v1",
        "formula_sha256": formula.sha256,
        "definition": formula.definition,
        "inputs": formula.inputs,
        "registers": formula.registers,
        "outputs": [
            {"name": row["name"], "type": row["type"]} for row in formula.outputs
        ],
        "specification": specification,
        "specification_sha256": _json_hash(specification),
        "solver": {
            "name": "z3",
            "version": z3.get_full_version(),
            "timeout_ms": timeout_ms,
        },
        "initialization": "declared",
        "bound": max_depth,
        "depths": [],
    }
    if retained_registers is not None:
        result.update(
            schema="pycircuit-rule-abstract-counterexample-v1",
            retained_registers=list(retained_registers),
        )
    solver = (solver_factory or z3.Solver)()
    solver.set(timeout=timeout_ms)
    states = [[z3.BitVec(f"s0_r{i}", width) for i, width in enumerate(formula.widths)]]
    solver.add(
        *[
            state == initial
            for state, initial in zip(states[0], formula.initials, strict=True)
        ]
    )
    inputs = []
    observation_inputs = _zero_inputs(formula)
    for depth in range(max_depth + 1):
        solver.push()
        solver.add(
            z3.Not(
                _encode(
                    formula, specification["property"], states[-1], observation_inputs
                )
            )
        )
        try:
            answer = (
                solver.check() if check_solver is None else check_solver(solver, depth)
            )
        except _SearchLimitError as error:
            result.update(status="resource_limit", reason=str(error))
            return result
        result["depths"].append({"depth": depth, "status": str(answer)})
        if answer == z3.unknown:
            result["status"] = "unknown"
            result["depths"][-1]["reason"] = solver.reason_unknown()
            return result
        if answer == z3.sat:
            solution = solver.model()

            def value(expression, solution=solution):
                actual = solution.eval(expression, model_completion=True)
                return (
                    int(z3.is_true(actual)) if z3.is_bool(actual) else actual.as_long()
                )

            rows = []
            for current, incoming in zip(
                states, [*inputs, observation_inputs], strict=True
            ):
                rows.append(
                    {
                        "inputs": [value(item) for item in incoming],
                        "state": [value(item) for item in current],
                        "outputs": [
                            value(_encode(formula, row["term"], current, incoming))
                            for row in formula.outputs
                        ],
                    }
                )
            result.update(
                status=(
                    "counterexample"
                    if retained_registers is None
                    else "abstract_counterexample"
                ),
                rows=rows,
                violation_depth=depth,
                shortest=True,
            )
            return result
        _require(answer == z3.unsat, "unexpected solver result")
        solver.pop()
        if depth < max_depth:
            incoming = [
                (
                    z3.Bool(f"i{depth}_{i}")
                    if kind == "bool"
                    else z3.BitVec(f"i{depth}_{i}", width)
                )
                for i, (kind, width) in enumerate(formula.input_types)
            ]
            current = states[-1]
            following = [
                z3.BitVec(f"s{depth + 1}_r{i}", width)
                for i, width in enumerate(formula.widths)
            ]
            solver.add(
                _encode(formula, specification["environment"], current, incoming)
            )
            solver.add(
                *[
                    register == _encode(formula, node, current, incoming)
                    for index, (register, node) in enumerate(
                        zip(following, formula.data["next"], strict=True)
                    )
                    if retained_registers is None or index in retained_registers
                ]
            )
            inputs.append(incoming)
            states.append(following)
    result["status"] = "bounded_unsat"
    return result


def validate_case(formula, case):
    """Check witness shape and identity; Lean separately checks its semantics."""
    _require(
        isinstance(case, dict)
        and case.get("schema") == "pycircuit-rule-counterexample-v1"
        and case.get("status") == "counterexample",
        "concrete counterexample required",
    )
    _require(
        case.get("formula_sha256") == formula.sha256
        and case.get("definition") == formula.definition,
        "case/formula identity mismatch",
    )
    _require(
        case.get("inputs") == formula.inputs
        and case.get("registers") == formula.registers
        and case.get("outputs")
        == [{"name": row["name"], "type": row["type"]} for row in formula.outputs],
        "case interface identity mismatch",
    )
    _require(
        case.get("initialization") == "declared",
        "reachable declared initialization required",
    )
    _specification(formula, case["specification"])
    _require(
        case.get("specification_sha256") == _json_hash(case["specification"]),
        "property identity mismatch",
    )
    depth = case.get("violation_depth")
    _require(_natural(depth) and depth <= 64, "invalid violation depth")
    rows = case.get("rows")
    _require(
        isinstance(rows, list) and len(rows) == depth + 1, "incomplete witness rows"
    )
    for row in rows:
        _require(
            isinstance(row, dict) and set(row) == {"inputs", "state", "outputs"},
            "invalid witness row",
        )
        for name, widths in (
            ("inputs", [t[1] for t in formula.input_types]),
            ("state", formula.widths),
            ("outputs", formula.output_widths),
        ):
            values = row[name]
            _require(
                isinstance(values, list) and len(values) == len(widths),
                "witness observation arity",
            )
            _require(
                all(
                    _natural(value) and value.bit_length() <= width
                    for value, width in zip(values, widths, strict=True)
                ),
                "witness value width",
            )
    _require(
        rows[-1]["inputs"] == [0] * len(formula.inputs),
        "final input must be observation-only zero",
    )


def _lean_expression(formula, node):
    def render(node, type_, children):
        op = node["op"]
        if op == "read":
            return f"(.reg {node['index']})"
        if op == "input":
            return f"(.input {node['index']})"
        if op == "boolLit":
            return f"(.boolLit {str(node['value']).lower()})"
        if op == "bitsLit":
            return f"(.bitsLit (BitVec.ofNat {type_[1]} {node['value']}))"
        return f"(.{op} {' '.join(children)})"

    return formula.fold(node, render)[1]


def _lean_input(formula, values):
    branches = []
    for index, ((kind, width), value) in enumerate(
        zip(formula.input_types, values, strict=True)
    ):
        literal = (
            str(bool(value)).lower()
            if kind == "bool"
            else f"(BitVec.ofNat {width} {value})"
        )
        branches.append(f"  | ⟨{index}, _⟩ => {literal}")
    count = len(formula.inputs)
    branches.append(
        f"  | ⟨n + {count}, bound⟩ => False.elim (by change n + {count} < {count} at bound; omega)"
    )
    return "fun index => match index with\n" + "\n".join(branches)


def _lean_identities(formula):
    identities = [
        f"definitionName = {json.dumps(formula.definition, ensure_ascii=False)}"
    ]
    for name, values in (
        ("inputNames", [r["name"] for r in formula.inputs]),
        ("registerNames", [r["name"] for r in formula.registers]),
        ("registerKeys", formula.owner_keys),
        ("outputNames", [r["name"] for r in formula.outputs]),
    ):
        identities.append(f"{name} = {json.dumps(values, ensure_ascii=False)}")
    identities.append(f"Witness.stateValues initialState = {formula.initials}")
    identities.append(f"List.ofFn signature.regWidth = {formula.widths}")
    input_types = [
        ".bool" if kind == "bool" else f".bits {width}"
        for kind, width in formula.input_types
    ]
    identities.append(
        "List.ofFn signature.inputType = [" + ", ".join(input_types) + "]"
    )
    identities.append(
        f"outputExpressions.map (fun output => output.width) = {formula.output_widths}"
    )
    return identities


def write_lean_witness(model_path, formula_path, case, destination):
    """Emit a kernel-checkable certificate, never execute the solver in Lean."""
    model_path, destination = Path(model_path), Path(destination)
    formula = RuleFormula.load(formula_path)
    validate_case(formula, case)
    model_hash = hashlib.sha256(model_path.read_bytes()).hexdigest()
    _require(
        case.get("model_sha256") == model_hash,
        "exported model identity mismatch",
    )
    property_ = _lean_expression(formula, case["specification"]["property"])
    environment = _lean_expression(formula, case["specification"]["environment"])
    definitions, rows = [], []
    for index, row in enumerate(case["rows"]):
        definitions.append(
            f"def input{index} : Inputs signature :=\n{_lean_input(formula, row['inputs'])}\n"
        )
        rows.append(
            f"{{ input := input{index}, state := {row['state']}, output := {row['outputs']} }}"
        )
    identities = _lean_identities(formula)
    content = (
        "import RuleSemantics.Witness\n" + model_path.read_text() + "\n"
        "namespace CounterexampleCertificate\nopen RuleSemantics RuleSemantics.Syntax PycircuitExport\n"
        + f"-- Model SHA256: {model_hash}; specification SHA256: {case['specification_sha256']}\n"
        + "theorem identity_checked : "
        + " ∧\n    ".join(identities)
        + " := ⟨"
        + ", ".join("rfl" for _ in identities)
        + "⟩\n"
        + f"def property : Expr signature .bool := {property_}\n"
        + f"def environment : Expr signature .bool := {environment}\n"
        + "\n".join(definitions)
        + "\ndef rows : List (Witness.Row signature) := [\n  "
        + ",\n  ".join(rows)
        + "]\n"
        + "theorem checked : Witness.check rules initialState outputExpressions property environment rows = true := by decide\n"
        + "theorem reachable : Witness.ReachableViolation rules initialState outputExpressions property environment rows :=\n"
        + "  Witness.check_sound rules initialState outputExpressions property environment rows checked\n"
        + "#print axioms identity_checked\n#print axioms checked\n#print axioms reachable\n"
        + "end CounterexampleCertificate\n"
    )
    destination.write_text(content)
    return destination
