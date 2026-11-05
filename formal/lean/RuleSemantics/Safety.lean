import RuleSemantics.Core

namespace RuleSemantics

/-- The local obligation concerns every accepted result, not only reachable tests. -/
def RulePreserves (invariant : State → Prop) (rule : Rule Input State Event) : Prop :=
  ∀ input state value candidate events, invariant state →
    rule input state = some (value, candidate, events) → invariant candidate

theorem runRule_preserves (invariant : State → Prop)
    (rule : Rule Input State Event) (safe : RulePreserves invariant rule)
    (input : Input) (state : State) (initial : invariant state) :
    invariant (runRule rule input state).1 := by
  cases outcome : rule input state with
  | none => simpa [runRule, outcome] using initial
  | some result =>
    rcases result with ⟨value, candidate, events⟩
    simpa [runRule, outcome] using safe input state value candidate events initial outcome

theorem schedule_preserves (invariant : State → Prop)
    (rules : List (Rule Input State Event))
    (safe : ∀ rule ∈ rules, RulePreserves invariant rule)
    (input : Input) (state : State) (initial : invariant state) :
    invariant (runSchedule rules input state).1 := by
  induction rules generalizing state with
  | nil => exact initial
  | cons rule rest ih =>
    change invariant (runSchedule rest input (runRule rule input state).1).1
    apply ih
    · intro next member
      exact safe next (List.mem_cons_of_mem rule member)
    · exact runRule_preserves invariant rule (safe rule (by simp)) input state initial

theorem history_preserves (invariant : State → Prop)
    (history : List (Cycle Input State Event))
    (safe : ∀ cycle ∈ history, ∀ rule ∈ cycle.1, RulePreserves invariant rule)
    (state : State) (initial : invariant state) :
    invariant (runHistory history state).1 := by
  induction history generalizing state with
  | nil => exact initial
  | cons cycle rest ih =>
    rcases cycle with ⟨rules, input⟩
    change invariant (runHistory rest (runSchedule rules input state).1).1
    apply ih
    · intro cycle member
      exact safe cycle (List.mem_cons_of_mem _ member)
    · exact schedule_preserves invariant rules (safe (rules, input) (by simp))
        input state initial

/-- Safety is established at every finite prefix, not only at the end of a run. -/
theorem history_prefix_preserves (invariant : State → Prop)
    (history : List (Cycle Input State Event))
    (safe : ∀ cycle ∈ history, ∀ rule ∈ cycle.1, RulePreserves invariant rule)
    (state : State) (initial : invariant state) (length : Nat) :
    invariant (runHistory (history.take length) state).1 := by
  apply history_preserves invariant (history.take length) _ state initial
  intro cycle member
  exact safe cycle (List.mem_of_mem_take member)

end RuleSemantics
