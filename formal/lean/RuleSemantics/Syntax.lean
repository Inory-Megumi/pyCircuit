import RuleSemantics.Safety

/-!
Closed, typed, two-state syntax interpreted independently as direct candidates
and compositional Actions. `require` denotes ordinary ineligibility, not an
assertion fault or a new pyCircuit source statement. Atomic roots and ordered
schedules reuse Core; this file does not parse or verify compiler output.
-/

namespace RuleSemantics.Syntax

inductive ValueType where
  | bool
  | bits (width : Nat)

abbrev ValueType.denote : ValueType → Type
  | .bool => Bool
  | .bits width => BitVec width

structure Signature where
  nr : Nat
  ni : Nat
  regWidth : Fin nr → Nat
  inputType : Fin ni → ValueType

abbrev State (signature : Signature) :=
  (register : Fin signature.nr) → BitVec (signature.regWidth register)

abbrev Inputs (signature : Signature) :=
  (index : Fin signature.ni) → (signature.inputType index).denote

def writeReg (state : State signature) (register : Fin signature.nr)
    (value : BitVec (signature.regWidth register)) : State signature :=
  fun other => if same : register = other then same ▸ value else state other

@[simp] theorem writeReg_same (state : State signature) (register : Fin signature.nr)
    (value : BitVec (signature.regWidth register)) :
    writeReg state register value register = value := by
  simp [writeReg]

@[simp] theorem writeReg_other (state : State signature) (register other : Fin signature.nr)
    (value : BitVec (signature.regWidth register)) (different : register ≠ other) :
    writeReg state register value other = state other := by
  simp [writeReg, different]

inductive Expr (signature : Signature) : ValueType → Type where
  | boolLit (value : Bool) : Expr signature .bool
  | bitsLit (value : BitVec width) : Expr signature (.bits width)
  | input (index : Fin signature.ni) : Expr signature (signature.inputType index)
  | reg (register : Fin signature.nr) : Expr signature (.bits (signature.regWidth register))
  | add (left right : Expr signature (.bits width)) : Expr signature (.bits width)
  | sub (left right : Expr signature (.bits width)) : Expr signature (.bits width)
  | ult (left right : Expr signature (.bits width)) : Expr signature .bool
  | eq (left right : Expr signature type) : Expr signature .bool
  | and (left right : Expr signature .bool) : Expr signature .bool
  | not (value : Expr signature .bool) : Expr signature .bool
  | ite (condition : Expr signature .bool) (yes no : Expr signature type) : Expr signature type
  | bit (value : Expr signature .bool) : Expr signature (.bits 1)
  | concat (high : Expr signature (.bits m)) (low : Expr signature (.bits n)) :
      Expr signature (.bits (m + n))

def valueEqual (type : ValueType) : type.denote → type.denote → Bool :=
  match type with
  | .bool => fun left right => left == right
  | .bits _ => fun left right => left == right

def evalExpr (expression : Expr signature type) (input : Inputs signature)
    (state : State signature) : type.denote :=
  match expression with
  | .boolLit value => value
  | .bitsLit value => value
  | .input index => input index
  | .reg register => state register
  | .add left right => evalExpr left input state + evalExpr right input state
  | .sub left right => evalExpr left input state - evalExpr right input state
  | .ult left right => (evalExpr left input state).ult (evalExpr right input state)
  | .eq left right => valueEqual _ (evalExpr left input state) (evalExpr right input state)
  | .and left right => evalExpr left input state && evalExpr right input state
  | .not value => !(evalExpr value input state)
  | .ite condition yes no =>
    if evalExpr condition input state then evalExpr yes input state else evalExpr no input state
  | .bit value => BitVec.ofBool (evalExpr value input state)
  | .concat high low => (evalExpr high input state).append (evalExpr low input state)

structure Output (signature : Signature) where
  width : Nat
  expression : Expr signature (.bits width)

inductive Command (signature : Signature) where
  | skip
  | assign (register : Fin signature.nr)
      (value : Expr signature (.bits (signature.regWidth register)))
  | seq (first second : Command signature)
  | require (condition : Expr signature .bool)

structure RuleDef (signature : Signature) where
  guard : Expr signature .bool
  body : Command signature

def evalCommand (command : Command signature) (input : Inputs signature)
    (state : State signature) : Option (State signature) :=
  match command with
  | .skip => some state
  | .assign register value => some (writeReg state register (evalExpr value input state))
  | .seq first second =>
    match evalCommand first input state with
    | none => none
    | some candidate => evalCommand second input candidate
  | .require condition => if evalExpr condition input state then some state else none

def evalRule (rule : RuleDef signature) (input : Inputs signature)
    (state : State signature) : Option (State signature) :=
  if evalExpr rule.guard input state then evalCommand rule.body input state else none

def interpretCommand (command : Command signature) (input : Inputs signature) :
    Action (State signature) Empty Unit :=
  match command with
  | .skip => Action.pure ()
  | .assign register value =>
    Action.modify (fun state => writeReg state register (evalExpr value input state))
  | .seq first second =>
    Action.bind (interpretCommand first input) (fun _ => interpretCommand second input)
  | .require condition => Action.guard (evalExpr condition input)

def interpretRule (rule : RuleDef signature) : Rule (Inputs signature) (State signature) Empty :=
  fun input => Action.bind (Action.guard (evalExpr rule.guard input))
    (fun _ => interpretCommand rule.body input)

def candidate (result : Option (State signature)) :
    Option (Unit × State signature × List Empty) :=
  result.map (fun state => ((), state, []))

def directRule (rule : RuleDef signature) : Rule (Inputs signature) (State signature) Empty :=
  fun input state => candidate (evalRule rule input state)

/-- Equality includes rejection, the full accepted candidate, and its empty effects. -/
theorem command_correspondence (command : Command signature) (input : Inputs signature)
    (state : State signature) :
    interpretCommand command input state = candidate (evalCommand command input state) := by
  induction command generalizing state with
  | skip => rfl
  | assign register value => rfl
  | require condition =>
    simp only [interpretCommand, Action.guard, evalCommand]
    split <;> rfl
  | seq first second ihFirst ihSecond =>
    simp only [interpretCommand, Action.bind, ihFirst, evalCommand]
    cases initial : evalCommand first input state with
    | none => rfl
    | some next =>
      simp only [candidate, Option.map_some]
      rw [ihSecond]
      cases evalCommand second input next <;> rfl

theorem rule_correspondence (rule : RuleDef signature) :
    interpretRule rule = directRule rule := by
  funext input state
  by_cases enabled : evalExpr rule.guard input state = true
  · cases outcome : evalCommand rule.body input state <;>
      simp [interpretRule, Action.bind, Action.guard, directRule, evalRule,
        enabled, command_correspondence, outcome, candidate]
  · simp [interpretRule, Action.bind, Action.guard, directRule, evalRule, enabled, candidate]

theorem runRule_correspondence (rule : RuleDef signature) (input : Inputs signature)
    (state : State signature) :
    runRule (interpretRule rule) input state = runRule (directRule rule) input state := by
  rw [rule_correspondence]

theorem schedule_correspondence (rules : List (RuleDef signature))
    (input : Inputs signature) (state : State signature) :
    runSchedule (rules.map interpretRule) input state =
      runSchedule (rules.map directRule) input state := by
  have same : interpretRule (signature := signature) = directRule :=
    funext rule_correspondence
  rw [same]

abbrev ASTCycle (signature : Signature) := List (RuleDef signature) × Inputs signature

def directCycle (cycle : ASTCycle signature) : Cycle (Inputs signature) (State signature) Empty :=
  (cycle.1.map directRule, cycle.2)

def interpretCycle (cycle : ASTCycle signature) : Cycle (Inputs signature) (State signature) Empty :=
  (cycle.1.map interpretRule, cycle.2)

theorem history_correspondence (history : List (ASTCycle signature)) (state : State signature) :
    runHistory (history.map interpretCycle) state = runHistory (history.map directCycle) state := by
  have same : interpretRule (signature := signature) = directRule :=
    funext rule_correspondence
  have cyclesSame : interpretCycle (signature := signature) = directCycle := by
    funext cycle
    simp only [interpretCycle, directCycle, same]
  rw [cyclesSame]

def LocallyPreserves (invariant : State signature → Prop) (rule : RuleDef signature) : Prop :=
  ∀ input state candidate, invariant state → evalRule rule input state = some candidate →
    invariant candidate

theorem invariant_transfer (invariant : State signature → Prop) (rule : RuleDef signature)
    (safe : LocallyPreserves invariant rule) :
    RulePreserves invariant (interpretRule rule) := by
  rw [rule_correspondence]
  intro input state value next events initial accepted
  unfold directRule candidate at accepted
  cases result : evalRule rule input state with
  | none => simp [result] at accepted
  | some candidate =>
    simp only [result, Option.map_some, Option.some.injEq, Prod.mk.injEq] at accepted
    rcases accepted with ⟨_, rfl, _⟩
    exact safe input state candidate initial result

theorem history_preserves (invariant : State signature → Prop)
    (history : List (ASTCycle signature))
    (safe : ∀ cycle ∈ history, ∀ rule ∈ cycle.1, LocallyPreserves invariant rule)
    (state : State signature) (initial : invariant state) :
    invariant (runHistory (history.map interpretCycle) state).1 := by
  apply RuleSemantics.history_preserves invariant _ _ state initial
  intro cycle member rule ruleMember
  rcases List.mem_map.mp member with ⟨source, sourceMember, rfl⟩
  rcases List.mem_map.mp ruleMember with ⟨sourceRule, sourceRuleMember, rfl⟩
  exact invariant_transfer invariant sourceRule (safe source sourceMember sourceRule sourceRuleMember)

theorem every_prefix_preserves (invariant : State signature → Prop)
    (history : List (ASTCycle signature))
    (safe : ∀ cycle ∈ history, ∀ rule ∈ cycle.1, LocallyPreserves invariant rule)
    (state : State signature) (initial : invariant state) (length : Nat) :
    invariant (runHistory ((history.take length).map interpretCycle) state).1 := by
  apply history_preserves invariant (history.take length) _ state initial
  intro cycle member rule ruleMember
  exact safe cycle (List.mem_of_mem_take member) rule ruleMember

end RuleSemantics.Syntax
