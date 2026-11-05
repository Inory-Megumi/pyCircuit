import RuleSemantics.Witness

/-!
Equation abstraction retains selected register updates from the actual Syntax
schedule. All state, input, initial, environment, and observation types stay
concrete. An omitted register update permits any value of its declared width.
-/

namespace RuleSemantics.Abstraction

open Syntax Witness

abbrev Mask (signature : Signature) := Fin signature.nr → Bool

def retain (mask : Mask signature) (added : Fin signature.nr) : Mask signature :=
  fun register => mask register || decide (register = added)

def Included (weaker stronger : Mask signature) : Prop :=
  ∀ register, weaker register = true → stronger register = true

def Step (rules : List (RuleDef signature)) (environment : Expr signature .bool)
    (mask : Mask signature) (input : Inputs signature)
    (state successor : State signature) : Prop :=
  evalExpr environment input state = true ∧
    ∀ register, mask register = true → successor register = nextState rules input state register

instance (rules : List (RuleDef signature)) (environment : Expr signature .bool)
    (mask : Mask signature) (input : Inputs signature) (state successor : State signature) :
    Decidable (Step rules environment mask input state successor) := by
  unfold Step
  infer_instance

theorem concrete_step (rules : List (RuleDef signature)) (environment : Expr signature .bool)
    (mask : Mask signature) (input : Inputs signature) (state : State signature)
    (allowed : evalExpr environment input state = true) :
    Step rules environment mask input state (nextState rules input state) :=
  ⟨allowed, fun _ _ => rfl⟩

theorem step_weaken {rules : List (RuleDef signature)} {environment : Expr signature .bool}
    {weaker stronger : Mask signature} (included : Included weaker stronger)
    {input : Inputs signature} {state successor : State signature}
    (step : Step rules environment stronger input state successor) :
    Step rules environment weaker input state successor :=
  ⟨step.1, fun register retained => step.2 register (included register retained)⟩

theorem retain_includes (mask : Mask signature) (added : Fin signature.nr) :
    Included mask (retain mask added) := by
  intro register retained
  simp [retain, retained]

theorem added_equation_excludes_edge (rules : List (RuleDef signature))
    (environment : Expr signature .bool) (mask : Mask signature)
    (added : Fin signature.nr) (input : Inputs signature) (state successor : State signature)
    (violated : successor added ≠ nextState rules input state added) :
    ¬ Step rules environment (retain mask added) input state successor := by
  intro step
  exact violated (step.2 added (by simp [retain]))

def decodeState (signature : Signature) (values : List Nat) : State signature :=
  fun register => BitVec.ofNat (signature.regWidth register) (values[register.val]?.getD 0)

@[simp] theorem decode_stateValues (state : State signature) :
    decodeState signature (stateValues state) = state := by
  funext register
  apply BitVec.eq_of_toNat_eq
  simp [decodeState, stateValues, register.isLt]

theorem stateValues_injective {first second : State signature}
    (observed : stateValues first = stateValues second) : first = second := by
  have decoded := congrArg (decodeState signature) observed
  simpa only [decode_stateValues] using decoded

inductive Trace (rules : List (RuleDef signature)) (outputs : List (Output signature))
    (environment : Expr signature .bool) (mask : Mask signature) :
    State signature → List (Witness.Row signature) → State signature → Prop where
  | final (state : State signature) (row : Witness.Row signature)
      (stateObserved : row.state = stateValues state)
      (outputObserved : row.output = outputValues outputs row.input state) :
      Trace rules outputs environment mask state [row] state
  | transition (state successor finalState : State signature) (row : Witness.Row signature)
      (rest : List (Witness.Row signature)) (stateObserved : row.state = stateValues state)
      (outputObserved : row.output = outputValues outputs row.input state)
      (step : Step rules environment mask row.input state successor)
      (later : Trace rules outputs environment mask successor rest finalState) :
      Trace rules outputs environment mask state (row :: rest) finalState

theorem trace_weaken {rules : List (RuleDef signature)} {outputs : List (Output signature)}
    {environment : Expr signature .bool} {weaker stronger : Mask signature}
    (included : Included weaker stronger) {initial finalState : State signature}
    {rows : List (Witness.Row signature)}
    (trace : Trace rules outputs environment stronger initial rows finalState) :
    Trace rules outputs environment weaker initial rows finalState := by
  induction trace with
  | final state row stateObserved outputObserved =>
    exact .final state row stateObserved outputObserved
  | transition state successor finalState row rest stateObserved outputObserved step later ih =>
    exact .transition state successor finalState row rest stateObserved outputObserved
      (step_weaken included step) ih

theorem concrete_trace {rules : List (RuleDef signature)} {outputs : List (Output signature)}
    {environment : Expr signature .bool} (mask : Mask signature)
    {initial finalState : State signature} {rows : List (Witness.Row signature)}
    (trace : Witness.Trace rules outputs environment initial rows finalState) :
    Trace rules outputs environment mask initial rows finalState := by
  induction trace with
  | final state row stateObserved outputObserved =>
    exact .final state row stateObserved outputObserved
  | transition state finalState row rest stateObserved outputObserved allowed later ih =>
    exact .transition state (nextState rules row.input state) finalState row rest
      stateObserved outputObserved (concrete_step rules environment mask row.input state allowed) ih

theorem history_coverage {rules : List (RuleDef signature)} {outputs : List (Output signature)}
    {environment : Expr signature .bool} (mask : Mask signature)
    {initial finalState : State signature} {rows : List (Witness.Row signature)}
    (trace : Witness.Trace rules outputs environment initial rows finalState) :
    Trace rules outputs environment mask initial rows finalState ∧
      (runHistory (transitionHistory rules rows) initial).1 = finalState :=
  ⟨concrete_trace mask trace, trace.history⟩

theorem bounded_safety_transfer (rules : List (RuleDef signature))
    (initial : State signature) (outputs : List (Output signature))
    (property environment : Expr signature .bool) (mask : Mask signature) (bound : Nat)
    (safe : ∀ rows finalState, Trace rules outputs environment mask initial rows finalState →
      rows.length ≤ bound + 1 → stateProperty property finalState = true)
    (rows : List (Witness.Row signature)) (finalState : State signature)
    (trace : Witness.Trace rules outputs environment initial rows finalState)
    (bounded : rows.length ≤ bound + 1) : stateProperty property finalState = true :=
  safe rows finalState (concrete_trace mask trace) bounded

theorem Trace.head_state {rules : List (RuleDef signature)} {outputs : List (Output signature)}
    {environment : Expr signature .bool} {mask : Mask signature}
    {initial finalState : State signature} {rows : List (Witness.Row signature)}
    (trace : Trace rules outputs environment mask initial rows finalState)
    (row : Witness.Row signature) (atHead : rows[0]? = some row) :
    row.state = stateValues initial := by
  cases trace <;> simp only [List.getElem?_cons_zero, Option.some.injEq] at atHead <;>
    subst row <;> assumption

theorem Trace.edge {rules : List (RuleDef signature)} {outputs : List (Output signature)}
    {environment : Expr signature .bool} {mask : Mask signature}
    {initial finalState : State signature} {rows : List (Witness.Row signature)}
    (trace : Trace rules outputs environment mask initial rows finalState)
    (index : Nat) (row following : Witness.Row signature)
    (atIndex : rows[index]? = some row) (atNext : rows[index + 1]? = some following) :
    Step rules environment mask row.input (decodeState signature row.state)
      (decodeState signature following.state) := by
  induction trace generalizing index with
  | final state last stateObserved outputObserved =>
    cases index <;> simp at atNext
  | transition state successor finalState first rest stateObserved outputObserved step later ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at atIndex
      subst row
      simp only [Nat.zero_add, List.getElem?_cons_succ] at atNext
      have nextObserved := later.head_state following atNext
      simpa only [stateObserved, nextObserved, decode_stateValues] using step
    | succ index =>
      simp only [List.getElem?_cons_succ] at atIndex atNext
      exact ih index atIndex atNext

theorem added_equation_excludes_trace (rules : List (RuleDef signature))
    (outputs : List (Output signature)) (environment : Expr signature .bool)
    (mask : Mask signature) (added : Fin signature.nr) (initial finalState : State signature)
    (rows : List (Witness.Row signature)) (index : Nat) (row following : Witness.Row signature)
    (atIndex : rows[index]? = some row) (atNext : rows[index + 1]? = some following)
    (violated : decodeState signature following.state added ≠
      nextState rules row.input (decodeState signature row.state) added) :
    ¬ Trace rules outputs environment (retain mask added) initial rows finalState := by
  intro trace
  exact added_equation_excludes_edge rules environment mask added row.input
    (decodeState signature row.state) (decodeState signature following.state) violated
    (trace.edge index row following atIndex atNext)

private def checkFrom (rules : List (RuleDef signature)) (outputs : List (Output signature))
    (property environment : Expr signature .bool) (mask : Mask signature)
    (rows : List (Witness.Row signature)) (current : State signature) : Bool :=
  match rows with
  | [] => false
  | row :: rest =>
    decide (row.state = stateValues current) &&
    decide (row.output = outputValues outputs row.input current) &&
    match rest with
    | [] => !(evalExpr property row.input current)
    | following :: _ =>
      let successor := decodeState signature following.state
      decide (Step rules environment mask row.input current successor) &&
        checkFrom rules outputs property environment mask rest successor

def check (rules : List (RuleDef signature)) (initialState : State signature)
    (outputs : List (Output signature)) (property environment : Expr signature .bool)
    (mask : Mask signature) (rows : List (Witness.Row signature)) : Bool :=
  stateOnly property && checkFrom rules outputs property environment mask rows initialState

private theorem checkFrom_sound (rules : List (RuleDef signature))
    (outputs : List (Output signature)) (property environment : Expr signature .bool)
    (mask : Mask signature) (pureProperty : stateOnly property = true)
    (rows : List (Witness.Row signature)) (initialState : State signature)
    (checked : checkFrom rules outputs property environment mask rows initialState = true) :
    ∃ finalState, Trace rules outputs environment mask initialState rows finalState ∧
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
    | cons following later =>
      have transitionChecked := Bool.and_eq_true_iff.mp components.2
      obtain ⟨finalState, trace, failed⟩ := ih _ transitionChecked.2
      exact ⟨finalState, .transition initialState (decodeState signature following.state)
        finalState row (following :: later) stateObserved outputObserved
        (of_decide_eq_true transitionChecked.1) trace, failed⟩

def Violation (rules : List (RuleDef signature)) (initialState : State signature)
    (outputs : List (Output signature)) (property environment : Expr signature .bool)
    (mask : Mask signature) (rows : List (Witness.Row signature)) : Prop :=
  stateOnly property = true ∧ ∃ finalState,
    Trace rules outputs environment mask initialState rows finalState ∧
      stateProperty property finalState = false

theorem check_sound (rules : List (RuleDef signature)) (initialState : State signature)
    (outputs : List (Output signature)) (property environment : Expr signature .bool)
    (mask : Mask signature) (rows : List (Witness.Row signature))
    (checked : check rules initialState outputs property environment mask rows = true) :
    Violation rules initialState outputs property environment mask rows := by
  have components := Bool.and_eq_true_iff.mp checked
  exact ⟨components.1, checkFrom_sound rules outputs property environment mask
    components.1 rows initialState components.2⟩

end RuleSemantics.Abstraction
