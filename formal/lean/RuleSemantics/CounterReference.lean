import RuleSemantics.BitVecCounter

/-!
A state-only combinational reference for a three-bit, capacity-five counter.
The increment candidate feeds decrement in the same cycle. The reference does
not emit events; the correspondence below concerns only the resulting state.
-/

namespace RuleSemantics.CounterReference

def step (input : Counter.Requests) (count : BitVec 3) : BitVec 3 :=
  let incCandidate :=
    if input.increment && count.ult (BitVec.ofNat 3 5) then count + 1 else count
  if input.decrement && (0 : BitVec 3).ult incCandidate then
    incCandidate - 1
  else incCandidate

def run (requests : List Counter.Requests) (count : BitVec 3) : BitVec 3 :=
  requests.foldl (fun state input => step input state) count

def requestHistory (requests : List Counter.Requests) : List Counter.CounterCycle :=
  requests.map (fun input => ([.increment, .decrement], input))

/-- The independently defined combinational step agrees for every three-bit state. -/
theorem step_refines (input : Counter.Requests) (count : BitVec 3) :
    step input count =
      (BitVecCounter.execute 3 5 [.increment, .decrement] input count).1 := by
  by_cases incrementEnabled : (input.increment && count.ult (BitVec.ofNat 3 5)) = true
  all_goals
    simp [step, BitVecCounter.execute, BitVecCounter.rule, runSchedule,
      runRule, BitVecCounter.increment, BitVecCounter.decrement, incrementEnabled]
    split <;> simp_all

/-- Finite request histories retain only the state of the fixed Rule schedule. -/
theorem run_refines (requests : List Counter.Requests) (count : BitVec 3) :
    run requests count =
      (BitVecCounter.executeHistory 3 5 (requestHistory requests) count).1 := by
  induction requests generalizing count with
  | nil => rfl
  | cons input rest ih =>
    change run rest (step input count) =
      (BitVecCounter.executeHistory 3 5 (requestHistory rest)
        (BitVecCounter.execute 3 5 [.increment, .decrement] input count).1).1
    rw [step_refines]
    exact ih _

/-- Nat correspondence requires no initial bound and makes no event claim. -/
theorem run_nat_refines (requests : List Counter.Requests) (count : BitVec 3) :
    (run requests count).toNat =
      (Counter.executeHistory 5 (requestHistory requests) count.toNat).1 := by
  have concreteSame := congrArg BitVec.toNat (run_refines requests count)
  have abstractSame := congrArg Prod.fst
    (BitVecCounter.history_refines 3 5 (by decide) (requestHistory requests) count)
  exact concreteSame.trans abstractSame

theorem run_bounded (requests : List Counter.Requests) (count : BitVec 3)
    (initial : count.toNat ≤ 5) :
    (run requests count).toNat ≤ 5 := by
  rw [run_nat_refines]
  exact Counter.history_bounded 5 (requestHistory requests) count.toNat initial

theorem every_prefix_bounded (requests : List Counter.Requests) (count : BitVec 3)
    (initial : count.toNat ≤ 5) (length : Nat) :
    (run (requests.take length) count).toNat ≤ 5 :=
  run_bounded (requests.take length) count initial

end RuleSemantics.CounterReference
