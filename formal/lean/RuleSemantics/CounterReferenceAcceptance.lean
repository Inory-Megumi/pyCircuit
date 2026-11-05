import RuleSemantics.CounterReference

/-!
Concrete state-only acceptance checks. The encoded-state enumeration includes
six and seven, which lie outside the capacity-five invariant. These checks use
direct kernel evaluation rather than the reference correspondence theorems.
-/

namespace RuleSemantics.CounterReferenceAcceptance

private def states : List (BitVec 3) := [0, 1, 2, 3, 4, 5, 6, 7]

private def requests : List Counter.Requests :=
  [⟨false, false⟩, ⟨true, false⟩, ⟨false, true⟩, ⟨true, true⟩]

private def both : Counter.Requests := ⟨true, true⟩

/-- Every encoded state and request combination agrees, including states above capacity. -/
theorem all_states_and_requests_agree :
    states.all (fun count => requests.all (fun input =>
      decide (CounterReference.step input count =
        (BitVecCounter.execute 3 5 [.increment, .decrement] input count).1))) = true := by
  decide

/-- The expected simultaneous-request states are specified independently as a table. -/
theorem both_requests_all_states :
    states.map (CounterReference.step both) = ([0, 1, 2, 3, 4, 4, 5, 6] : List (BitVec 3)) ∧
    states.map (fun count =>
      (BitVecCounter.execute 3 5 [.increment, .decrement] both count).1) =
        ([0, 1, 2, 3, 4, 4, 5, 6] : List (BitVec 3)) := by
  decide

/-- At empty, decrement sees the increment candidate; reversing the schedule ends at one. -/
theorem both_requests_at_empty :
    CounterReference.step both 0 = 0 ∧
    (BitVecCounter.execute 3 5 [.decrement, .increment] both 0).1 = 1 := by
  decide

/-- At capacity, increment rejects before decrement; reversing the schedule refills it. -/
theorem both_requests_at_capacity :
    CounterReference.step both 5 = 4 ∧
    (BitVecCounter.execute 3 5 [.decrement, .increment] both 5).1 = 5 := by
  decide

end RuleSemantics.CounterReferenceAcceptance
