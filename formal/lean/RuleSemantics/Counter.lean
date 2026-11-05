import RuleSemantics.Safety

namespace RuleSemantics.Counter

structure Requests where
  increment : Bool
  decrement : Bool
  deriving Repr, DecidableEq

inductive Event where
  | incremented
  | decremented
  deriving Repr, DecidableEq

inductive Operation where
  | increment
  | decrement
  deriving Repr, DecidableEq

/-- Unrestricted Nat state; boundedness must be proved, not encoded in its type. -/
def increment (capacity : Nat) : Rule Requests Nat Event :=
  fun input count =>
    if input.increment && decide (count < capacity) then
      some ((), count + 1, [.incremented])
    else none

def decrement : Rule Requests Nat Event :=
  fun input count =>
    if input.decrement && decide (0 < count) then
      some ((), count - 1, [.decremented])
    else none

def rule (capacity : Nat) : Operation → Rule Requests Nat Event
  | .increment => increment capacity
  | .decrement => decrement

theorem increment_preserves (capacity : Nat) :
    RulePreserves (fun count => count ≤ capacity) (increment capacity) := by
  intro input count value candidate events initial accepted
  unfold increment at accepted
  split at accepted
  · rename_i enabled
    have bound : count < capacity := by simpa using (Bool.and_eq_true_iff.mp enabled).2
    cases accepted
    omega
  · contradiction

theorem decrement_preserves (capacity : Nat) :
    RulePreserves (fun count => count ≤ capacity) decrement := by
  intro input count value candidate events initial accepted
  unfold decrement at accepted
  split at accepted
  · cases accepted
    omega
  · contradiction

theorem rule_preserves (capacity : Nat) (operation : Operation) :
    RulePreserves (fun count => count ≤ capacity) (rule capacity operation) := by
  cases operation with
  | increment => exact increment_preserves capacity
  | decrement => exact decrement_preserves capacity

def execute (capacity : Nat) (operations : List Operation) (input : Requests)
    (count : Nat) : Nat × List Event :=
  runSchedule (operations.map (rule capacity)) input count

theorem schedule_bounded (capacity : Nat) (operations : List Operation)
    (input : Requests) (count : Nat) (initial : count ≤ capacity) :
    (execute capacity operations input count).1 ≤ capacity := by
  apply schedule_preserves (fun count => count ≤ capacity) _ _ input count initial
  intro candidate member
  rcases List.mem_map.mp member with ⟨operation, _, rfl⟩
  exact rule_preserves capacity operation

abbrev CounterCycle := List Operation × Requests

def expandCycle (capacity : Nat) (cycle : CounterCycle) : Cycle Requests Nat Event :=
  (cycle.1.map (rule capacity), cycle.2)

def executeHistory (capacity : Nat) (history : List CounterCycle) (count : Nat) :
    Nat × List Event :=
  runHistory (history.map (expandCycle capacity)) count

theorem history_bounded (capacity : Nat) (history : List CounterCycle)
    (count : Nat) (initial : count ≤ capacity) :
    (executeHistory capacity history count).1 ≤ capacity := by
  apply history_preserves (fun count => count ≤ capacity) _ _ count initial
  intro cycle member candidate candidateMember
  rcases List.mem_map.mp member with ⟨source, _, rfl⟩
  rcases List.mem_map.mp candidateMember with ⟨operation, _, rfl⟩
  exact rule_preserves capacity operation

theorem every_prefix_bounded (capacity : Nat) (history : List CounterCycle)
    (count : Nat) (initial : count ≤ capacity) (length : Nat) :
    (executeHistory capacity (history.take length) count).1 ≤ capacity :=
  history_bounded capacity (history.take length) count initial

def both : Requests := ⟨true, true⟩

theorem increment_then_decrement (capacity : Nat) (positive : 0 < capacity) :
    execute capacity [.increment, .decrement] both 0 =
      (0, [.incremented, .decremented]) := by
  simp [execute, rule, runSchedule, runRule, increment, decrement, both, positive]

theorem decrement_then_increment (capacity : Nat) (positive : 0 < capacity) :
    execute capacity [.decrement, .increment] both 0 = (1, [.incremented]) := by
  simp [execute, rule, runSchedule, runRule, increment, decrement, both, positive]

theorem order_changes_behavior (capacity : Nat) (positive : 0 < capacity) :
    (execute capacity [.increment, .decrement] both 0).1 ≠
      (execute capacity [.decrement, .increment] both 0).1 := by
  rw [increment_then_decrement capacity positive, decrement_then_increment capacity positive]
  decide

/-- Two updates in one root have one rejection boundary. -/
def mergedIncrements (capacity : Nat) : Rule Requests Nat Event :=
  fun input => Action.bind (increment capacity input) (fun _ => increment capacity input)

theorem independent_roots_keep_first :
    execute 1 [.increment, .increment] both 0 = (1, [.incremented]) := by
  decide

theorem merged_root_rolls_back :
    runRule (mergedIncrements 1) both 0 = (0, []) := by
  decide

theorem merging_changes_behavior :
    execute 1 [.increment, .increment] both 0 ≠
      runRule (mergedIncrements 1) both 0 := by
  decide

theorem zero_capacity_holds (operations : List Operation) (input : Requests) :
    (execute 0 operations input 0).1 = 0 := by
  have bound := schedule_bounded 0 operations input 0 (by omega)
  omega

end RuleSemantics.Counter
