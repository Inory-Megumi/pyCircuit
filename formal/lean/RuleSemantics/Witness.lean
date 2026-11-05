import RuleSemantics.Syntax

/-!
Concrete full-trace checking against the actual closed Syntax interpreter.
Rows observe cycle-entry state. Every row except the last supplies a transition
input and satisfies the environment. The last input supplies only an output
observation, and the state-only property fails at that final reachable state.
-/

namespace RuleSemantics.Witness

open Syntax

structure Row (signature : Signature) where
  input : Inputs signature
  state : List Nat
  output : List Nat

def stateValues (state : State signature) : List Nat :=
  List.ofFn (fun register => (state register).toNat)

def outputValues (outputs : List (Output signature)) (input : Inputs signature)
    (state : State signature) : List Nat :=
  outputs.map (fun (output : Output signature) => (evalExpr output.expression input state).toNat)

def stateOnly : Expr signature type → Bool
  | .boolLit _ | .bitsLit _ | .reg _ => true
  | .input _ => false
  | .add left right | .sub left right | .ult left right | .eq left right | .and left right =>
    stateOnly left && stateOnly right
  | .not value | .bit value => stateOnly value
  | .concat high low => stateOnly high && stateOnly low
  | .ite condition yes no => stateOnly condition && stateOnly yes && stateOnly no

theorem stateOnly_input_irrelevant (expression : Expr signature type)
    (checked : stateOnly expression = true) (first second : Inputs signature)
    (state : State signature) :
    evalExpr expression first state = evalExpr expression second state := by
  induction expression <;> simp_all [stateOnly, evalExpr, Bool.and_eq_true]

def defaultInputs (signature : Signature) : Inputs signature := fun index =>
  match signature.inputType index with
  | .bool => false
  | .bits _ => 0

def stateProperty (property : Expr signature .bool) (state : State signature) : Bool :=
  evalExpr property (defaultInputs signature) state

def nextState (rules : List (RuleDef signature)) (input : Inputs signature)
    (state : State signature) : State signature :=
  (runSchedule (rules.map interpretRule) input state).1

def transitionHistory (rules : List (RuleDef signature)) (rows : List (Row signature)) :
    List (Cycle (Inputs signature) (State signature) Empty) :=
  rows.dropLast.map (fun row => (rules.map interpretRule, row.input))

def stateAt (rules : List (RuleDef signature)) (initialState : State signature)
    (rows : List (Row signature)) (index : Nat) : State signature :=
  (runHistory ((rows.take index).map (fun row => (rules.map interpretRule, row.input))) initialState).1

private def checkFrom (rules : List (RuleDef signature)) (outputs : List (Output signature))
    (property environment : Expr signature .bool) (rows : List (Row signature))
    (current : State signature) : Bool :=
  match rows with
  | [] => false
  | row :: rest =>
    decide (row.state = stateValues current) &&
    decide (row.output = outputValues outputs row.input current) &&
    match rest with
    | [] => !(evalExpr property row.input current)
    | _ :: _ => evalExpr environment row.input current &&
      checkFrom rules outputs property environment rest (nextState rules row.input current)

def check (rules : List (RuleDef signature)) (initialState : State signature)
    (outputs : List (Output signature)) (property environment : Expr signature .bool)
    (rows : List (Row signature)) : Bool :=
  stateOnly property && checkFrom rules outputs property environment rows initialState

/-- Every observation is tied to an actual Core transition from the declared entry. -/
inductive Trace (rules : List (RuleDef signature)) (outputs : List (Output signature))
    (environment : Expr signature .bool) : State signature → List (Row signature) →
      State signature → Prop where
  | final (state : State signature) (row : Row signature)
      (stateObserved : row.state = stateValues state)
      (outputObserved : row.output = outputValues outputs row.input state) :
      Trace rules outputs environment state [row] state
  | transition (state finalState : State signature) (row : Row signature)
      (rest : List (Row signature)) (stateObserved : row.state = stateValues state)
      (outputObserved : row.output = outputValues outputs row.input state)
      (allowed : evalExpr environment row.input state = true)
      (later : Trace rules outputs environment (nextState rules row.input state) rest finalState) :
      Trace rules outputs environment state (row :: rest) finalState

theorem Trace.nonempty {signature : Signature} {rules : List (RuleDef signature)}
    {outputs : List (Output signature)} {environment : Expr signature .bool}
    {initial finalState : State signature} {rows : List (Row signature)}
    (trace : Trace rules outputs environment initial rows finalState) : rows ≠ [] := by
  cases trace <;> simp

private theorem checkFrom_sound (rules : List (RuleDef signature))
    (outputs : List (Output signature)) (property environment : Expr signature .bool)
    (pureProperty : stateOnly property = true) (rows : List (Row signature))
    (initialState : State signature)
    (checked : checkFrom rules outputs property environment rows initialState = true) :
    ∃ finalState, Trace rules outputs environment initialState rows finalState ∧
      stateProperty property finalState = false := by
  induction rows generalizing initialState with
  | nil => simp [checkFrom] at checked
  | cons row rest ih =>
    have components := Bool.and_eq_true_iff.mp checked
    have observed := Bool.and_eq_true_iff.mp components.1
    have stateObserved : row.state = stateValues initialState := of_decide_eq_true observed.1
    have outputObserved : row.output = outputValues outputs row.input initialState :=
      of_decide_eq_true observed.2
    cases rest with
    | nil =>
      refine ⟨initialState, .final initialState row stateObserved outputObserved, ?_⟩
      have failed : evalExpr property row.input initialState = false := by
        simpa only [checkFrom, Bool.not_eq_true'] using components.2
      rw [stateProperty, ← stateOnly_input_irrelevant property pureProperty row.input
        (defaultInputs signature) initialState]
      exact failed
    | cons next later =>
      have transitionChecked := Bool.and_eq_true_iff.mp components.2
      obtain ⟨finalState, trace, failed⟩ := ih _ transitionChecked.2
      exact ⟨finalState, .transition initialState finalState row (next :: later)
        stateObserved outputObserved transitionChecked.1 trace, failed⟩

theorem Trace.history {signature : Signature} {rules : List (RuleDef signature)}
    {outputs : List (Output signature)} {environment : Expr signature .bool}
    {initial finalState : State signature} {rows : List (Row signature)}
    (trace : Trace rules outputs environment initial rows finalState) :
    (runHistory (transitionHistory rules rows) initial).1 = finalState := by
  induction trace with
  | final state row stateObserved outputObserved => rfl
  | transition state finalState row rest stateObserved outputObserved allowed later ih =>
    have nonempty := later.nonempty
    cases rest with
    | nil => contradiction
    | cons next rest =>
      simpa only [transitionHistory, List.dropLast_cons_cons, List.map_cons, runHistory,
        nextState] using ih

theorem Trace.observations {signature : Signature} {rules : List (RuleDef signature)}
    {outputs : List (Output signature)} {environment : Expr signature .bool}
    {initial finalState : State signature} {rows : List (Row signature)}
    (trace : Trace rules outputs environment initial rows finalState)
    (index : Nat) (row : Row signature) (atIndex : rows[index]? = some row) :
    row.state = stateValues (stateAt rules initial rows index) ∧
      row.output = outputValues outputs row.input (stateAt rules initial rows index) := by
  induction trace generalizing index with
  | final state last stateObserved outputObserved =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at atIndex
      subst row
      exact ⟨stateObserved, outputObserved⟩
    | succ index => simp at atIndex
  | transition state finalState first rest stateObserved outputObserved allowed later ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at atIndex
      subst row
      exact ⟨stateObserved, outputObserved⟩
    | succ index =>
      simp only [List.getElem?_cons_succ] at atIndex
      simpa only [stateAt, List.take_succ_cons, List.map_cons, runHistory, nextState] using
        ih index atIndex

theorem Trace.environment {signature : Signature} {rules : List (RuleDef signature)}
    {outputs : List (Output signature)} {constraint : Expr signature .bool}
    {initial finalState : State signature} {rows : List (Row signature)}
    (trace : Trace rules outputs constraint initial rows finalState)
    (index : Nat) (row : Row signature) (atIndex : rows[index]? = some row)
    (transitioning : index + 1 < rows.length) :
    evalExpr constraint row.input (stateAt rules initial rows index) = true := by
  induction trace generalizing index with
  | final state last stateObserved outputObserved =>
    simp only [List.length_singleton] at transitioning
    omega
  | transition state finalState first rest stateObserved outputObserved allowed later ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at atIndex
      subst row
      exact allowed
    | succ index =>
      simp only [List.getElem?_cons_succ] at atIndex
      have nextTransitioning : index + 1 < rest.length := by
        simp only [List.length_cons] at transitioning
        omega
      simpa only [stateAt, List.take_succ_cons, List.map_cons, runHistory, nextState] using
        ih index atIndex nextTransitioning

def ReachableViolation (rules : List (RuleDef signature)) (initialState : State signature)
    (outputs : List (Output signature)) (property environment : Expr signature .bool)
    (rows : List (Row signature)) : Prop :=
  stateOnly property = true ∧ ∃ finalState,
    Trace rules outputs environment initialState rows finalState ∧
      (runHistory (transitionHistory rules rows) initialState).1 = finalState ∧
      stateProperty property finalState = false

theorem check_sound (rules : List (RuleDef signature)) (initialState : State signature)
    (outputs : List (Output signature)) (property environment : Expr signature .bool)
    (rows : List (Row signature)) (checked : check rules initialState outputs property environment rows = true) :
    ReachableViolation rules initialState outputs property environment rows := by
  have parts := Bool.and_eq_true_iff.mp checked
  obtain ⟨finalState, trace, failed⟩ := checkFrom_sound rules outputs property environment
    parts.1 rows initialState parts.2
  exact ⟨parts.1, finalState, trace, trace.history, failed⟩

theorem check_observations (rules : List (RuleDef signature)) (initialState : State signature)
    (outputs : List (Output signature)) (property environment : Expr signature .bool)
    (rows : List (Row signature)) (checked : check rules initialState outputs property environment rows = true)
    (index : Nat) (row : Row signature) (atIndex : rows[index]? = some row) :
    row.state = stateValues (stateAt rules initialState rows index) ∧
      row.output = outputValues outputs row.input (stateAt rules initialState rows index) := by
  obtain ⟨_, finalState, trace, _, _⟩ := check_sound rules initialState outputs property environment rows checked
  exact trace.observations index row atIndex

end RuleSemantics.Witness
