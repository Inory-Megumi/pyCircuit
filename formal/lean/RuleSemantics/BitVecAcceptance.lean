import RuleSemantics.BitVecCounter

/-!
Independent literal outcomes for the finite-width abstract counter.
Width zero is a mathematical BitVec boundary, not a pyCircuit source width.
-/

namespace RuleSemantics.BitVecAcceptance

theorem last_increment_then_full_rejection :
    BitVecCounter.execute 3 7 [.increment, .increment] Counter.both 6 =
      (7, [.incremented]) := by
  decide

theorem zero_does_not_underflow :
    BitVecCounter.execute 3 7 [.decrement] Counter.both 0 = (0, []) := by
  decide

theorem order_sensitive_cycle :
    BitVecCounter.execute 2 3 [.increment, .decrement] Counter.both 0 =
      (0, [.incremented, .decremented]) ∧
    BitVecCounter.execute 2 3 [.decrement, .increment] Counter.both 0 =
      (1, [.incremented]) := by
  decide

def variedHistory : List Counter.CounterCycle :=
  [ ([.increment, .increment], ⟨true, false⟩),
    ([.increment, .decrement], ⟨true, true⟩),
    ([.decrement, .decrement, .increment], ⟨false, true⟩),
    ([.increment, .decrement], ⟨true, false⟩) ]

theorem changing_inputs_history :
    BitVecCounter.executeHistory 3 5 variedHistory 3 =
      (3, [.incremented, .incremented, .decremented,
        .decremented, .decremented, .incremented]) := by
  decide

theorem zero_capacity_boundaries :
    BitVecCounter.execute 0 0 [.increment, .decrement, .increment] Counter.both 0 =
      (0, []) ∧
    BitVecCounter.execute 3 0 [.decrement, .increment] Counter.both 0 =
      (0, []) := by
  decide

/-- An unrepresentable capacity wraps to zero and changes acceptance itself. -/
theorem unrepresentable_capacity_differs_from_nat :
    BitVecCounter.execute 2 4 [.increment] Counter.both 0 = (0, []) ∧
    Counter.execute 4 [.increment] Counter.both 0 = (1, [.incremented]) := by
  decide

end RuleSemantics.BitVecAcceptance
