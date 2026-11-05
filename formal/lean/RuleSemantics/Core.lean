import Std

/-!
An abstract, two-state model of independently accepted atomic rules.
`none` means ordinary ineligibility, never a fault or whole-system failure.
Intermediate schedule states are candidate versions within one successful cycle.
Events are abstract effects, not pyCircuit's sampled log-publication protocol.
-/

namespace RuleSemantics

abbrev Action (State Event Value : Type) :=
  State → Option (Value × State × List Event)

namespace Action

def pure (value : Value) : Action State Event Value :=
  fun state => some (value, state, [])

def bind (first : Action State Event Value)
    (next : Value → Action State Event Result) : Action State Event Result :=
  fun state =>
    match first state with
    | none => none
    | some (value, candidate, events) =>
      match next value candidate with
      | none => none
      | some (result, finalState, laterEvents) =>
        some (result, finalState, events ++ laterEvents)

def guard (enabled : State → Bool) : Action State Event Unit :=
  fun state => if enabled state then some ((), state, []) else none

def modify (update : State → State) : Action State Event Unit :=
  fun state => some ((), update state, [])

def emit (event : Event) : Action State Event Unit :=
  fun state => some ((), state, [event])

theorem bind_rejects_left (first : Action State Event Value)
    (next : Value → Action State Event Result) (state : State)
    (rejected : first state = none) :
    bind first next state = none := by
  simp [bind, rejected]

theorem bind_rejects_right (first : Action State Event Value)
    (next : Value → Action State Event Result) (state candidate : State)
    (value : Value) (events : List Event)
    (accepted : first state = some (value, candidate, events))
    (rejected : next value candidate = none) :
    bind first next state = none := by
  simp [bind, accepted, rejected]

theorem bind_forwards (first : Action State Event Value)
    (next : Value → Action State Event Result) (state candidate finalState : State)
    (value : Value) (result : Result) (events laterEvents : List Event)
    (accepted : first state = some (value, candidate, events))
    (laterAccepted : next value candidate = some (result, finalState, laterEvents)) :
    bind first next state = some (result, finalState, events ++ laterEvents) := by
  simp [bind, accepted, laterAccepted]

/-- Reassociating helper calls within one root preserves state and event order. -/
theorem bind_assoc (first : Action State Event Value)
    (next : Value → Action State Event Intermediate)
    (last : Intermediate → Action State Event Result) :
    bind (bind first next) last = bind first (fun value => bind (next value) last) := by
  funext state
  cases initial : first state with
  | none => simp [bind, initial]
  | some result =>
    rcases result with ⟨value, candidate, events⟩
    cases middle : next value candidate with
    | none => simp [bind, initial, middle]
    | some result =>
      rcases result with ⟨intermediate, laterState, laterEvents⟩
      cases final : last intermediate laterState with
      | none => simp [bind, initial, middle, final]
      | some result =>
        rcases result with ⟨result, finalState, finalEvents⟩
        simp [bind, initial, middle, final, List.append_assoc]

end Action

abbrev Rule (Input State Event : Type) := Input → Action State Event Unit

/-- An outer atomic boundary: reject all candidate state and effects together. -/
def runRule (rule : Rule Input State Event) (input : Input) (state : State) :
    State × List Event :=
  match rule input state with
  | none => (state, [])
  | some (_, candidate, events) => (candidate, events)

/-- Each root has its own boundary; all roots share this cycle's input. -/
def runSchedule (rules : List (Rule Input State Event)) (input : Input)
    (state : State) : State × List Event :=
  match rules with
  | [] => (state, [])
  | rule :: rest =>
    let first := runRule rule input state
    let later := runSchedule rest input first.1
    (later.1, first.2 ++ later.2)

abbrev Cycle (Input State Event : Type) := List (Rule Input State Event) × Input

/-- Both inputs and schedules may vary from one cycle to the next. -/
def runHistory (history : List (Cycle Input State Event)) (state : State) :
    State × List Event :=
  match history with
  | [] => (state, [])
  | (rules, input) :: rest =>
    let first := runSchedule rules input state
    let later := runHistory rest first.1
    (later.1, first.2 ++ later.2)

theorem rejected_rule_holds (rule : Rule Input State Event) (input : Input)
    (state : State) (rejected : rule input state = none) :
    runRule rule input state = (state, []) := by
  simp [runRule, rejected]

theorem rejected_successor_preserves_predecessor
    (first second : Rule Input State Event) (input : Input) (state : State)
    (rejected : second input (runRule first input state).1 = none) :
    runSchedule [first, second] input state = runRule first input state := by
  simp only [runSchedule]
  rw [rejected_rule_holds second input (runRule first input state).1 rejected]
  simp

end RuleSemantics
