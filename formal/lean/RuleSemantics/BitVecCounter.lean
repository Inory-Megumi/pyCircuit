import RuleSemantics.Counter
import RuleSemantics.Refinement

/-!
A separately defined finite-width implementation of the guarded Nat counter.
Unsigned comparisons and modular arithmetic operate on BitVec values. Projection
to Nat appears only in specifications and proofs, not in these transitions.
-/

namespace RuleSemantics.BitVecCounter

open Counter (Requests Event Operation CounterCycle)

def increment (width capacity : Nat) : Rule Requests (BitVec width) Event :=
  fun input count =>
    if input.increment && count.ult (BitVec.ofNat width capacity) then
      some ((), count + BitVec.ofNat width 1, [.incremented])
    else none

def decrement (width : Nat) : Rule Requests (BitVec width) Event :=
  fun input count =>
    if input.decrement && (BitVec.ofNat width 0).ult count then
      some ((), count - BitVec.ofNat width 1, [.decremented])
    else none

def rule (width capacity : Nat) : Operation → Rule Requests (BitVec width) Event
  | .increment => increment width capacity
  | .decrement => decrement width

def execute (width capacity : Nat) (operations : List Operation) (input : Requests)
    (count : BitVec width) : BitVec width × List Event :=
  runSchedule (operations.map (rule width capacity)) input count

def executeHistory (width capacity : Nat) (history : List CounterCycle)
    (count : BitVec width) : BitVec width × List Event :=
  runHistory (history.map (Refinement.expandCycle (rule width capacity))) count

theorem increment_guard_agrees (width capacity : Nat)
    (fits : capacity < 2 ^ width) (count : BitVec width) :
    count.ult (BitVec.ofNat width capacity) = decide (count.toNat < capacity) := by
  rw [BitVec.ult_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]

theorem decrement_guard_agrees (width : Nat) (count : BitVec width) :
    (BitVec.ofNat width 0).ult count = decide (0 < count.toNat) := by
  simp [BitVec.ult_eq_decide]

/-- Only the enabled branch needs one to be representable; width zero cannot enable it. -/
theorem increment_value_agrees (width capacity : Nat) (fits : capacity < 2 ^ width)
    (count : BitVec width) (below : count.toNat < capacity) :
    (count + BitVec.ofNat width 1).toNat = count.toNat + 1 := by
  have oneFits : 1 < 2 ^ width := by omega
  have oneValue : (BitVec.ofNat width 1).toNat = 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt oneFits]
  rw [BitVec.toNat_add, oneValue, Nat.mod_eq_of_lt (by omega)]

theorem decrement_value_agrees (width : Nat) (count : BitVec width)
    (positive : 0 < count.toNat) :
    (count - BitVec.ofNat width 1).toNat = count.toNat - 1 := by
  have stateFits := count.isLt
  have oneFits : 1 < 2 ^ width := by omega
  have oneValue : (BitVec.ofNat width 1).toNat = 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt oneFits]
  have enough : BitVec.ofNat width 1 ≤ count := by
    rw [BitVec.le_def, oneValue]
    omega
  rw [BitVec.toNat_sub_of_le enough, oneValue]

/-- Complete candidate equality includes ordinary rejection and accepted events. -/
theorem increment_refines (width capacity : Nat) (fits : capacity < 2 ^ width) :
    Refinement.RuleRefines BitVec.toNat (increment width capacity)
      (Counter.increment capacity) := by
  intro input count
  unfold increment Counter.increment
  rw [increment_guard_agrees width capacity fits count]
  by_cases enabled : (input.increment && decide (count.toNat < capacity)) = true
  · have below : count.toNat < capacity := by
      simpa using (Bool.and_eq_true_iff.mp enabled).2
    simp [enabled, Refinement.projectCandidate,
      increment_value_agrees width capacity fits count below]
  · simp [enabled, Refinement.projectCandidate]

theorem decrement_refines (width : Nat) :
    Refinement.RuleRefines BitVec.toNat (decrement width) Counter.decrement := by
  intro input count
  unfold decrement Counter.decrement
  rw [decrement_guard_agrees width count]
  by_cases enabled : (input.decrement && decide (0 < count.toNat)) = true
  · have positive : 0 < count.toNat := by
      simpa using (Bool.and_eq_true_iff.mp enabled).2
    simp [enabled, Refinement.projectCandidate,
      decrement_value_agrees width count positive]
  · simp [enabled, Refinement.projectCandidate]

theorem rule_refines (width capacity : Nat) (fits : capacity < 2 ^ width)
    (operation : Operation) :
    Refinement.RuleRefines BitVec.toNat (rule width capacity operation)
      (Counter.rule capacity operation) := by
  cases operation with
  | increment => exact increment_refines width capacity fits
  | decrement => exact decrement_refines width

/-- Correspondence requires no initially bounded-state premise. -/
theorem schedule_refines (width capacity : Nat) (fits : capacity < 2 ^ width)
    (operations : List Operation) (input : Requests) (count : BitVec width) :
    Refinement.projectResult BitVec.toNat (execute width capacity operations input count) =
      Counter.execute capacity operations input count.toNat := by
  exact Refinement.schedule_refines BitVec.toNat (rule width capacity)
    (Counter.rule capacity) (rule_refines width capacity fits) operations input count

theorem history_refines (width capacity : Nat) (fits : capacity < 2 ^ width)
    (history : List CounterCycle) (count : BitVec width) :
    Refinement.projectResult BitVec.toNat (executeHistory width capacity history count) =
      Counter.executeHistory capacity history count.toNat := by
  exact Refinement.history_refines BitVec.toNat (rule width capacity)
    (Counter.rule capacity) (rule_refines width capacity fits) history count

theorem every_prefix_refines (width capacity : Nat) (fits : capacity < 2 ^ width)
    (history : List CounterCycle) (count : BitVec width) (length : Nat) :
    Refinement.projectResult BitVec.toNat
      (executeHistory width capacity (history.take length) count) =
      Counter.executeHistory capacity (history.take length) count.toNat :=
  history_refines width capacity fits (history.take length) count

theorem schedule_bounded (width capacity : Nat) (fits : capacity < 2 ^ width)
    (operations : List Operation) (input : Requests) (count : BitVec width)
    (initial : count.toNat ≤ capacity) :
    (execute width capacity operations input count).1.toNat ≤ capacity := by
  have same := congrArg Prod.fst (schedule_refines width capacity fits operations input count)
  change (execute width capacity operations input count).1.toNat =
    (Counter.execute capacity operations input count.toNat).1 at same
  rw [same]
  exact Counter.schedule_bounded capacity operations input count.toNat initial

theorem history_bounded (width capacity : Nat) (fits : capacity < 2 ^ width)
    (history : List CounterCycle) (count : BitVec width)
    (initial : count.toNat ≤ capacity) :
    (executeHistory width capacity history count).1.toNat ≤ capacity := by
  have same := congrArg Prod.fst (history_refines width capacity fits history count)
  change (executeHistory width capacity history count).1.toNat =
    (Counter.executeHistory capacity history count.toNat).1 at same
  rw [same]
  exact Counter.history_bounded capacity history count.toNat initial

theorem every_prefix_bounded (width capacity : Nat) (fits : capacity < 2 ^ width)
    (history : List CounterCycle) (count : BitVec width)
    (initial : count.toNat ≤ capacity) (length : Nat) :
    (executeHistory width capacity (history.take length) count).1.toNat ≤ capacity :=
  history_bounded width capacity fits (history.take length) count initial

end RuleSemantics.BitVecCounter
