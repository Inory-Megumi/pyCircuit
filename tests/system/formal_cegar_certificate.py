"""Generate kernel-checked equation-refinement certificates for exported Syntax."""

from __future__ import annotations

import hashlib
from pathlib import Path

from formal_counterexample import (
    _lean_expression,
    _lean_identities,
    _lean_input,
    validate_case,
)
from formal_rule_model import RuleFormula, _natural, _require


def _mask(indices, register_count):
    _require(
        isinstance(indices, list)
        and all(_natural(index) and index < register_count for index in indices)
        and len(set(indices)) == len(indices),
        "invalid retained-register inventory",
    )
    return f"fun register => decide (register.val ∈ ({indices} : List Nat))"


def write_lean_refinement(model_path, formula_path, iteration, destination):
    """Check one full abstract path and its selected added Syntax equation."""
    model_path, destination = Path(model_path), Path(destination)
    formula = RuleFormula.load(formula_path)
    case, refinement = iteration["search"], iteration["refinement"]
    _require(
        case.get("schema") == "pycircuit-rule-abstract-counterexample-v1"
        and case.get("status") == "abstract_counterexample"
        and iteration.get("concretization", {}).get("status") == "unsat",
        "a spurious abstract counterexample refinement is required",
    )
    validate_case(
        formula,
        {
            **case,
            "schema": "pycircuit-rule-counterexample-v1",
            "status": "counterexample",
        },
    )
    model_hash = hashlib.sha256(model_path.read_bytes()).hexdigest()
    _require(case.get("model_sha256") == model_hash, "exported model identity mismatch")
    retained = iteration["retained_registers"]
    _require(
        case.get("retained_registers") == retained,
        "iteration and abstract candidate retained registers differ",
    )
    old_mask = _mask(retained, len(formula.registers))
    new_mask = _mask(refinement["retained_registers"], len(formula.registers))
    added, edge = refinement["register"], refinement["edge"]
    _require(
        _natural(added)
        and added < len(formula.registers)
        and _natural(edge)
        and edge + 1 < len(case["rows"]),
        "invalid selected register or transition edge",
    )
    identities = _lean_identities(formula)
    definitions, row_names = [], []
    for index, row in enumerate(case["rows"]):
        definitions.append(
            f"def input{index} : Inputs signature :=\n{_lean_input(formula, row['inputs'])}\n"
            f"def row{index} : Witness.Row signature :=\n"
            f"  {{ input := input{index}, state := {row['state']}, output := {row['outputs']} }}\n"
        )
        row_names.append(f"row{index}")
    property_ = _lean_expression(formula, case["specification"]["property"])
    environment = _lean_expression(formula, case["specification"]["environment"])
    content = (
        "import RuleSemantics.Abstraction\n"
        + model_path.read_text()
        + "\nnamespace RefinementCertificate\n"
        + "open RuleSemantics RuleSemantics.Syntax PycircuitExport\n"
        + f"-- Model SHA256: {model_hash}; specification SHA256: {case['specification_sha256']}\n"
        + "theorem identity_checked : "
        + " ∧\n    ".join(identities)
        + " := ⟨"
        + ", ".join("rfl" for _ in identities)
        + "⟩\n"
        + f"def property : Expr signature .bool := {property_}\n"
        + f"def environment : Expr signature .bool := {environment}\n"
        + "\n".join(definitions)
        + "\ndef rows : List (Witness.Row signature) := ["
        + ", ".join(row_names)
        + "]\n"
        + f"def oldMask : Abstraction.Mask signature := {old_mask}\n"
        + f"def newMask : Abstraction.Mask signature := {new_mask}\n"
        + f"def added : Fin signature.nr := ⟨{added}, by decide⟩\n"
        + "theorem added_omitted : oldMask added = false := by decide\n"
        + "theorem new_mask_is_retain : newMask = Abstraction.retain oldMask added := by\n"
        + "  funext register\n"
        + "  have checked : ∀ index, newMask index = Abstraction.retain oldMask added index := by decide\n"
        + "  exact checked register\n"
        + "theorem old_in_new : Abstraction.Included oldMask newMask := by\n"
        + "  rw [new_mask_is_retain]\n"
        + "  exact Abstraction.retain_includes oldMask added\n"
        + "theorem old_admitted :\n"
        + "    Abstraction.check rules initialState outputExpressions property environment oldMask rows = true := by decide\n"
        + "theorem old_violation :\n"
        + "    Abstraction.Violation rules initialState outputExpressions property environment oldMask rows :=\n"
        + "  Abstraction.check_sound rules initialState outputExpressions property environment oldMask rows old_admitted\n"
        + "theorem equation_violated :\n"
        + f"    Abstraction.decodeState signature row{edge + 1}.state added ≠\n"
        + f"      Witness.nextState rules row{edge}.input (Abstraction.decodeState signature row{edge}.state) added := by decide\n"
        + "theorem new_rejected :\n"
        + "    Abstraction.check rules initialState outputExpressions property environment newMask rows = false := by decide\n"
        + "theorem path_excluded (finalState : State signature) :\n"
        + "    ¬ Abstraction.Trace rules outputExpressions environment newMask initialState rows finalState := by\n"
        + "  rw [new_mask_is_retain]\n"
        + "  exact Abstraction.added_equation_excludes_trace rules outputExpressions environment oldMask added\n"
        + f"    initialState finalState rows {edge} row{edge} row{edge + 1} rfl rfl equation_violated\n"
        + "theorem concrete_in_new (input : Inputs signature) (state : State signature)\n"
        + "    (allowed : evalExpr environment input state = true) :\n"
        + "    Abstraction.Step rules environment newMask input state (Witness.nextState rules input state) :=\n"
        + "  Abstraction.concrete_step rules environment newMask input state allowed\n"
        + "theorem new_in_old (input : Inputs signature) (state successor : State signature)\n"
        + "    (step : Abstraction.Step rules environment newMask input state successor) :\n"
        + "    Abstraction.Step rules environment oldMask input state successor :=\n"
        + "  Abstraction.step_weaken old_in_new step\n"
        + "theorem refined_trace_in_old (traceRows : List (Witness.Row signature))\n"
        + "    (initial finalState : State signature)\n"
        + "    (trace : Abstraction.Trace rules outputExpressions environment newMask initial traceRows finalState) :\n"
        + "    Abstraction.Trace rules outputExpressions environment oldMask initial traceRows finalState :=\n"
        + "  Abstraction.trace_weaken old_in_new trace\n"
    )
    for theorem in (
        "identity_checked",
        "added_omitted",
        "new_mask_is_retain",
        "old_in_new",
        "old_admitted",
        "old_violation",
        "equation_violated",
        "new_rejected",
        "path_excluded",
        "concrete_in_new",
        "new_in_old",
        "refined_trace_in_old",
    ):
        content += f"#print axioms {theorem}\n"
    destination.write_text(content + "end RefinementCertificate\n")
    return destination
