import RuleSemantics.Counter

/-!
Independent acceptance examples for the abstract successful-cycle model.
The composite-state examples exercise complete rollback, effect retention at
independent root boundaries, and reads of an earlier candidate update.
The history expectations below are literal counts and ordered abstract events.
-/

namespace RuleSemantics.Acceptance

abbrev PairState := Nat × Nat

/-- Update both fields and record the complete state seen before the update. -/
def prepare : Action PairState PairState Unit :=
  fun state =>
    Action.bind (Action.modify (fun current : PairState =>
      (current.1 + 3, current.2 + 5)))
      (fun _ => Action.emit state) state

def prepareRoot : Rule Unit PairState PairState :=
  fun _ => prepare

def rejectRoot : Rule Unit PairState PairState :=
  fun _ => Action.guard (fun _ => false)

def prepareThenReject : Rule Unit PairState PairState :=
  fun _ => Action.bind prepare (fun _ => Action.guard (fun _ => false))

theorem composite_root_rolls_back (left right : Nat) :
    runRule prepareThenReject () (left, right) = ((left, right), []) := by
  simp [runRule, prepareThenReject, prepare, Action.bind, Action.modify,
    Action.emit, Action.guard]

theorem independent_rejection_keeps_earlier_effects (left right : Nat) :
    runSchedule [prepareRoot, rejectRoot] () (left, right) =
      ((left + 3, right + 5), [(left, right)]) := by
  simp [runSchedule, runRule, prepareRoot, rejectRoot, prepare, Action.bind,
    Action.modify, Action.emit, Action.guard]

def prepareThenObserve (expected : Nat) : Rule Unit PairState PairState :=
  fun _ => Action.bind prepare
    (fun _ => Action.guard (fun current => decide (current.1 = expected)))

/-- The read-only condition observes the prior update within the same root. -/
theorem later_condition_sees_candidate (left right : Nat) :
    runRule (prepareThenObserve (left + 3)) () (left, right) =
      ((left + 3, right + 5), [(left, right)]) := by
  simp [runRule, prepareThenObserve, prepare, Action.bind, Action.modify,
    Action.emit, Action.guard]

open Counter

/-- Inputs and schedule order both change between successful cycles. -/
def variedHistory : List CounterCycle :=
  [ ([.decrement, .increment, .increment], ⟨true, false⟩),
    ([.increment, .decrement], ⟨true, true⟩),
    ([.decrement, .increment], ⟨false, true⟩),
    ([.increment, .decrement, .increment], ⟨true, false⟩),
    ([.decrement, .increment, .decrement], ⟨true, true⟩) ]

theorem varied_history_has_expected_count_and_events :
    executeHistory 2 variedHistory 0 =
      (1, [.incremented, .incremented, .decremented, .decremented,
        .incremented, .incremented, .decremented, .incremented, .decremented]) := by
  decide

theorem zero_capacity_history_has_no_effects :
    executeHistory 0 variedHistory 0 = (0, []) := by
  decide

end RuleSemantics.Acceptance
