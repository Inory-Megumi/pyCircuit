import RuleSemantics.Core

/-!
State projection preserves complete abstract observations: rejection, accepted
values, and ordered events. The local obligation covers every input and state.
-/

namespace RuleSemantics.Refinement

def projectResult (project : Concrete → Abstract)
    (result : Concrete × List Event) : Abstract × List Event :=
  (project result.1, result.2)

def projectCandidate (project : Concrete → Abstract)
    (candidate : Option (Value × Concrete × List Event)) :
    Option (Value × Abstract × List Event) :=
  match candidate with
  | none => none
  | some (value, state, events) => some (value, project state, events)

def RuleRefines (project : Concrete → Abstract)
    (concreteRule : Rule Input Concrete Event)
    (abstractRule : Rule Input Abstract Event) : Prop :=
  ∀ input state,
    projectCandidate project (concreteRule input state) = abstractRule input (project state)

theorem runRule_refines (project : Concrete → Abstract)
    (concreteRule : Rule Input Concrete Event)
    (abstractRule : Rule Input Abstract Event)
    (refines : RuleRefines project concreteRule abstractRule)
    (input : Input) (state : Concrete) :
    projectResult project (runRule concreteRule input state) =
      runRule abstractRule input (project state) := by
  have localRefinement := refines input state
  cases outcome : concreteRule input state with
  | none =>
    simp only [outcome, projectCandidate] at localRefinement
    simp [runRule, outcome, ← localRefinement, projectResult]
  | some result =>
    rcases result with ⟨value, candidate, events⟩
    simp only [outcome, projectCandidate] at localRefinement
    simp [runRule, outcome, ← localRefinement, projectResult]

theorem schedule_refines (project : Concrete → Abstract)
    (concreteRules : Op → Rule Input Concrete Event)
    (abstractRules : Op → Rule Input Abstract Event)
    (refines : ∀ operation, RuleRefines project (concreteRules operation)
      (abstractRules operation))
    (operations : List Op) (input : Input) (state : Concrete) :
    projectResult project (runSchedule (operations.map concreteRules) input state) =
      runSchedule (operations.map abstractRules) input (project state) := by
  induction operations generalizing state with
  | nil => simp [runSchedule, projectResult]
  | cons operation rest ih =>
    have first := runRule_refines project (concreteRules operation)
      (abstractRules operation) (refines operation) input state
    have later := ih (runRule (concreteRules operation) input state).1
    simp only [projectResult] at first later
    simp [runSchedule, ← first, ← later, projectResult]

def expandCycle (rules : Op → Rule Input State Event)
    (cycle : List Op × Input) : Cycle Input State Event :=
  (cycle.1.map rules, cycle.2)

/-- Inputs and operation lists may change at every cycle. -/
theorem history_refines (project : Concrete → Abstract)
    (concreteRules : Op → Rule Input Concrete Event)
    (abstractRules : Op → Rule Input Abstract Event)
    (refines : ∀ operation, RuleRefines project (concreteRules operation)
      (abstractRules operation))
    (history : List (List Op × Input)) (state : Concrete) :
    projectResult project (runHistory (history.map (expandCycle concreteRules)) state) =
      runHistory (history.map (expandCycle abstractRules)) (project state) := by
  induction history generalizing state with
  | nil => simp [runHistory, projectResult]
  | cons cycle rest ih =>
    rcases cycle with ⟨operations, input⟩
    have first := schedule_refines project concreteRules abstractRules refines
      operations input state
    have later := ih (runSchedule (operations.map concreteRules) input state).1
    simp only [projectResult] at first later
    simp [expandCycle, runHistory, ← first, ← later, projectResult]

end RuleSemantics.Refinement
