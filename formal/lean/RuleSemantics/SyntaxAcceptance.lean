import RuleSemantics.SyntaxCounter

/-! Independent literal outcomes for closed typed Rule syntax. -/

namespace RuleSemantics.SyntaxAcceptance

open Syntax

abbrev heterogeneous : Signature where
  nr := 2
  ni := 2
  regWidth register := if register.val = 0 then 3 else 5
  inputType := Fin.cases (.bits 3) (fun _ => .bool)

def inputs : Inputs heterogeneous :=
  Fin.cases (2 : BitVec 3) (fun _ => true)

def pairState (narrow wide : Nat) : State heterogeneous :=
  fun register => BitVec.ofNat _ (if register.val = 0 then narrow else wide)

private theorem pair_state_eq {actual expected : State heterogeneous}
    (narrow : actual 0 = expected 0) (wide : actual 1 = expected 1) :
    actual = expected := by
  funext register
  have alternatives : register.val = 0 ∨ register.val = 1 := by
    have bound : register.val < 2 := register.isLt
    omega
  rcases alternatives with first | second
  · have same : register = 0 := Fin.ext first
    subst register
    exact narrow
  · have same : register = 1 := Fin.ext second
    subst register
    exact wide

private theorem pair_result_eq (actual : State heterogeneous × List Empty)
    (narrow wide : Nat)
    (first : actual.1 0 = (pairState narrow wide) 0)
    (second : actual.1 1 = (pairState narrow wide) 1) :
    actual = (pairState narrow wide, []) := by
  apply Prod.ext
  · exact pair_state_eq first second
  · cases actual.2 with
    | nil => rfl
    | cons event _ => cases event

def forwarded : RuleDef heterogeneous where
  guard := .and (.input 1) (.not (.ult (.reg 0) (.bitsLit 6)))
  body := .seq (.assign 0 (.add (.reg 0) (.input 0)))
    (.seq (.assign 1 (.add (.reg 1) (.bitsLit 3)))
      (.seq (.assign 0 (.add (.reg 0) (.reg 0)))
        (.seq (.assign 1 (.add (.reg 1) (.reg 1)))
          (.require (.eq (.reg 1) (.bitsLit 4))))))

/-- Both interpreters must reach literal state (2,4), including both modular wraps. -/
theorem heterogeneous_forwarding :
    runRule (directRule forwarded) inputs (pairState 7 31) = (pairState 2 4, []) ∧
    runRule (interpretRule forwarded) inputs (pairState 7 31) = (pairState 2 4, []) := by
  constructor <;> apply pair_result_eq <;> decide

def updateBoth : RuleDef heterogeneous where
  guard := .boolLit true
  body := .seq (.assign 0 (.add (.reg 0) (.bitsLit 1)))
    (.assign 1 (.add (.reg 1) (.bitsLit 1)))

def requireBelowSix : RuleDef heterogeneous where
  guard := .boolLit true
  body := .require (.ult (.reg 0) (.bitsLit 6))

def updateThenReject : RuleDef heterogeneous where
  guard := .boolLit true
  body := .seq updateBoth.body requireBelowSix.body

/-- Ordinary ineligibility is none inside each interpretation, before root holding. -/
theorem late_require_rejects_candidate :
    evalRule updateThenReject inputs (pairState 5 12) = none ∧
    interpretRule updateThenReject inputs (pairState 5 12) = none := by
  constructor <;> rfl

theorem late_require_rolls_back_both_registers :
    runRule (directRule updateThenReject) inputs (pairState 5 12) = (pairState 5 12, []) ∧
    runRule (interpretRule updateThenReject) inputs (pairState 5 12) = (pairState 5 12, []) := by
  constructor <;> apply pair_result_eq <;> decide

theorem separate_roots_retain_preceding_writes :
    runSchedule ([updateBoth, requireBelowSix].map directRule) inputs (pairState 5 12) =
      (pairState 6 13, []) ∧
    runSchedule ([updateBoth, requireBelowSix].map interpretRule) inputs (pairState 5 12) =
      (pairState 6 13, []) := by
  constructor <;> apply pair_result_eq <;> decide

private theorem counter_result_eq
    (actual : State SyntaxCounter.signature × List Empty) (expected : BitVec 3)
    (observed : actual.1 0 = expected) : actual = (SyntaxCounter.state expected, []) := by
  apply Prod.ext
  · funext register
    have same : register = 0 := Subsingleton.elim _ _
    subst register
    exact observed
  · cases actual.2 with
    | nil => rfl
    | cons event _ => cases event

/-- Both interpretations distinguish the two explicit root orders at the empty boundary. -/
theorem counter_ordering :
    (runSchedule ([SyntaxCounter.increment, SyntaxCounter.decrement].map directRule)
        (SyntaxCounter.inputs Counter.both) (SyntaxCounter.state 0) =
      (SyntaxCounter.state 0, []) ∧
    runSchedule ([SyntaxCounter.decrement, SyntaxCounter.increment].map directRule)
        (SyntaxCounter.inputs Counter.both) (SyntaxCounter.state 0) =
      (SyntaxCounter.state 1, [])) ∧
    (runSchedule ([SyntaxCounter.increment, SyntaxCounter.decrement].map interpretRule)
        (SyntaxCounter.inputs Counter.both) (SyntaxCounter.state 0) =
      (SyntaxCounter.state 0, []) ∧
    runSchedule ([SyntaxCounter.decrement, SyntaxCounter.increment].map interpretRule)
        (SyntaxCounter.inputs Counter.both) (SyntaxCounter.state 0) =
      (SyntaxCounter.state 1, [])) := by
  constructor <;> constructor <;> apply counter_result_eq <;> decide

end RuleSemantics.SyntaxAcceptance
