import RuleSemantics.Syntax
import RuleSemantics.CounterReference

/-!
One counter AST interpreted by the generic syntax semantics. Correspondence
observes state only and reuses the existing reference/Nat history proofs.
The Python-to-AST mapping is manually reviewed, not automatically extracted.
-/

namespace RuleSemantics.SyntaxCounter

open Syntax

abbrev signature : Signature :=
  { nr := 1, ni := 2, regWidth := fun _ => 3, inputType := fun _ => .bool }

def inputs (request : Counter.Requests) : Inputs signature :=
  fun index => if index.val = 0 then request.increment else request.decrement

def state (count : BitVec 3) : State signature := fun _ => count

def observe (current : State signature) : BitVec 3 := current 0

theorem state_observe (current : State signature) : state (observe current) = current := by
  funext register
  have same : register = 0 := Subsingleton.elim _ _
  subst register
  rfl

def increment : RuleDef signature :=
  { guard := .and (.input 0) (.ult (.reg 0) (.bitsLit 5))
    body := .assign 0 (.add (.reg 0) (.bitsLit 1)) }

def decrement : RuleDef signature :=
  { guard := .and (.input 1) (.ult (.bitsLit 0) (.reg 0))
    body := .assign 0 (.sub (.reg 0) (.bitsLit 1)) }

def rules : List (RuleDef signature) := [increment, decrement]

theorem write_state (current : State signature) (value : BitVec 3) :
    writeReg current 0 value = state value := by
  funext register
  have same : register = 0 := Subsingleton.elim _ _
  subst register
  simp [state]

def execute (request : Counter.Requests) (count : BitVec 3) : BitVec 3 :=
  observe (runSchedule (rules.map interpretRule) (inputs request) (state count)).1

def history (requests : List Counter.Requests) : List (ASTCycle signature) :=
  requests.map (fun request => (rules, inputs request))

def executeHistory (requests : List Counter.Requests) (count : BitVec 3) : BitVec 3 :=
  observe (runHistory ((history requests).map interpretCycle) (state count)).1

/-- The AST's two roots forward the increment candidate to decrement. -/
theorem step_refines (request : Counter.Requests) (count : BitVec 3) :
    execute request count = CounterReference.step request count := by
  unfold execute
  rw [schedule_correspondence]
  cases incrementEnabled : request.increment && count.ult (BitVec.ofNat 3 5) with
  | false =>
    cases decrementEnabled : request.decrement && (BitVec.ofNat 3 0).ult count <;>
      simp [rules, increment, decrement, runSchedule, runRule, directRule, candidate,
        evalRule, evalCommand, evalExpr, inputs, state, observe, write_state,
        CounterReference.step, incrementEnabled, decrementEnabled]
  | true =>
    cases decrementEnabled : request.decrement &&
        (BitVec.ofNat 3 0).ult (count + BitVec.ofNat 3 1) <;>
      simp [rules, increment, decrement, runSchedule, runRule, directRule, candidate,
        evalRule, evalCommand, evalExpr, inputs, state, observe, write_state,
        CounterReference.step, incrementEnabled, decrementEnabled]

/-- Every state of the singleton register bank has the same observed cycle behavior. -/
theorem cycle_state (request : Counter.Requests) (current : State signature) :
    (runSchedule (rules.map interpretRule) (inputs request) current).1 =
      state (CounterReference.step request (observe current)) := by
  rw [← state_observe (runSchedule (rules.map interpretRule) (inputs request) current).1]
  rw [← state_observe current]
  exact congrArg state (step_refines request (observe current))

theorem history_refines (requests : List Counter.Requests) (count : BitVec 3) :
    executeHistory requests count = CounterReference.run requests count := by
  induction requests generalizing count with
  | nil => rfl
  | cons request rest ih =>
    change observe (runHistory ((history rest).map interpretCycle)
      (runSchedule (rules.map interpretRule) (inputs request) (state count)).1).1 =
        CounterReference.run rest (CounterReference.step request count)
    rw [cycle_state]
    exact ih _

theorem history_nat_refines (requests : List Counter.Requests) (count : BitVec 3) :
    (executeHistory requests count).toNat =
      (Counter.executeHistory 5 (CounterReference.requestHistory requests) count.toNat).1 := by
  rw [history_refines]
  exact CounterReference.run_nat_refines requests count

theorem history_bounded (requests : List Counter.Requests) (count : BitVec 3)
    (initial : count.toNat ≤ 5) : (executeHistory requests count).toNat ≤ 5 := by
  rw [history_refines]
  exact CounterReference.run_bounded requests count initial

theorem every_prefix_bounded (requests : List Counter.Requests) (count : BitVec 3)
    (initial : count.toNat ≤ 5) (length : Nat) :
    (executeHistory (requests.take length) count).toNat ≤ 5 :=
  history_bounded (requests.take length) count initial

end RuleSemantics.SyntaxCounter
