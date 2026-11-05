import RuleSemantics.Contracts
import RuleSemantics.CounterReference

/-!
Concrete closed ASTs and independent list specifications for the bounded source
library. FIFO payloads are arbitrary; only occupancy zero/one/two and request
controls are split in proofs. Encoded occupancy three is excluded explicitly
from queue refinement. Actual exported-source connections are separate kernel
obligations, and no theorem here certifies a native Queue resource.
-/

namespace RuleSemantics.Library

open Syntax

abbrev Payload := BitVec 8

structure Requests where
  put : Bool
  data : Payload
  take : Bool

theorem bit_roundtrip (value : BitVec 1) : BitVec.ofBool (value == 1) = value := by
  have bound := value.isLt
  have cases : value.toNat = 0 ∨ value.toNat = 1 := by omega
  rcases cases with zero | one
  · have equal : value = (0 : BitVec 1) := BitVec.eq_of_toNat_eq zero
    rw [equal]; rfl
  · have equal : value = (1 : BitVec 1) := BitVec.eq_of_toNat_eq one
    rw [equal]; rfl

def cycle (rules : List (RuleDef signature)) (input : Inputs signature) (state : State signature) :
    State signature := (runSchedule (rules.map interpretRule) input state).1

def runRequests (rules : List (RuleDef signature)) (bind : Requests → Inputs signature)
    (requests : List Requests) (state : State signature) : State signature :=
  (runHistory (requests.map (fun request => (rules.map interpretRule, bind request))) state).1

theorem runRequests_cons (rules : List (RuleDef signature)) (bind : Requests → Inputs signature)
    (request : Requests) (rest : List Requests) (state : State signature) :
    runRequests rules bind (request :: rest) state =
      runRequests rules bind rest (cycle rules (bind request) state) := rfl

namespace Queue

def pop (request : Requests) (queue : List Payload) : List Payload :=
  if request.take then queue.tail else queue

def push (capacity : Nat) (request : Requests) (queue : List Payload) : List Payload :=
  if request.put && decide (queue.length < capacity) then queue ++ [request.data] else queue

def step (capacity : Nat) (request : Requests) (queue : List Payload) : List Payload :=
  push capacity request (pop request queue)

def run (capacity : Nat) (requests : List Requests) (queue : List Payload) : List Payload :=
  requests.foldl (fun current request => step capacity request current) queue

def observation (capacity : Nat) (request : Requests) (queue : List Payload) : BitVec 10 :=
  (BitVec.ofBool (decide (queue.length < capacity) || (request.take && !queue.isEmpty))).append
    ((BitVec.ofBool (!queue.isEmpty)).append (queue.headD 0))

theorem step_bounded (capacity : Nat) (request : Requests) (queue : List Payload)
    (initial : queue.length ≤ capacity) : (step capacity request queue).length ≤ capacity := by
  have removed : (pop request queue).length ≤ capacity := by
    unfold pop
    split
    · simp only [List.length_tail]; omega
    · exact initial
  unfold step push
  split
  · rename_i enabled
    have below : (pop request queue).length < capacity := by
      simpa using (Bool.and_eq_true_iff.mp enabled).2
    simp only [List.length_append, List.length_singleton]
    omega
  · exact removed

theorem run_bounded (capacity : Nat) (requests : List Requests) (queue : List Payload)
    (initial : queue.length ≤ capacity) : (run capacity requests queue).length ≤ capacity := by
  induction requests generalizing queue with
  | nil => exact initial
  | cons request rest ih => exact ih _ (step_bounded capacity request queue initial)

end Queue

namespace Register8

abbrev signature : Signature :=
  { nr := 1, ni := 2, regWidth := fun _ => 8
    inputType := fun i => match i.val with | 0 => .bits 1 | _ => .bits 8 }

def initialState : State signature := fun _ => 0
def update : RuleDef signature :=
  { guard := .eq (.input 0) (.bitsLit 1)
    body := .seq (.assign 0 (.input 1)) .skip }
def rules := [update]
def outputExpressions : List (Output signature) := [⟨8, .reg 0⟩]

def inputs (write : Bool) (data : Payload) : Inputs signature := fun i =>
  match i with
  | ⟨0, _⟩ => if write then (1 : BitVec 1) else (0 : BitVec 1)
  | ⟨1, _⟩ => data
  | ⟨n + 2, h⟩ => False.elim (by change n + 2 < 2 at h; omega)

theorem cycle_correct (write : Bool) (data : Payload) (state : State signature) :
    cycle rules (inputs write data) state 0 = if write then data else state 0 := by
  cases write <;> rfl

theorem bounded (state : State signature) : (state 0).toNat < 256 := (state 0).isLt

theorem initial_zero : initialState 0 = 0 := rfl

end Register8

namespace Counter3

abbrev signature : Signature :=
  { nr := 1, ni := 2, regWidth := fun _ => 3, inputType := fun _ => .bits 1 }
def initialState : State signature := fun _ => 0
def increment : RuleDef signature :=
  { guard := .and (.eq (.input 0) (.bitsLit 1)) (.ult (.reg 0) (.bitsLit 5))
    body := .seq (.assign 0 (.add (.reg 0) (.bitsLit 1))) .skip }
def decrement : RuleDef signature :=
  { guard := .and (.eq (.input 1) (.bitsLit 1)) (.ult (.bitsLit 0) (.reg 0))
    body := .seq (.assign 0 (.sub (.reg 0) (.bitsLit 1))) .skip }
def rules := [increment, decrement]
def outputExpressions : List (Output signature) := [⟨3, .reg 0⟩]
def inputs (request : Counter.Requests) : Inputs signature :=
  fun i => if i.val = 0 then BitVec.ofBool request.increment else BitVec.ofBool request.decrement

theorem cycle_correct (request : Counter.Requests) (state : State signature) :
    cycle rules (inputs request) state 0 = CounterReference.step request (state 0) := by
  cases request with
  | mk inc dec =>
    cases inc <;> cases dec <;>
      simp [signature, cycle, rules, increment, decrement, runSchedule, Contracts.runRule_empty,
        Contracts.step_direct, evalRule, evalCommand, evalExpr, valueEqual, inputs,
        BitVec.ofBool, CounterReference.step]
    all_goals split <;> simp_all
    all_goals split <;> simp_all

def run (requests : List Counter.Requests) (state : State signature) : State signature :=
  (runHistory (requests.map (fun request => (rules.map interpretRule, inputs request))) state).1

theorem history_refines (requests : List Counter.Requests) (state : State signature) :
    run requests state 0 = CounterReference.run requests (state 0) := by
  induction requests generalizing state with
  | nil => rfl
  | cons request rest ih =>
    change run rest (cycle rules (inputs request) state) 0 = _
    rw [ih, cycle_correct]
    rfl

theorem history_nat_refines (requests : List Counter.Requests) (state : State signature) :
    (run requests state 0).toNat =
      (Counter.executeHistory 5 (CounterReference.requestHistory requests) (state 0).toNat).1 := by
  rw [history_refines]
  exact CounterReference.run_nat_refines requests (state 0)

theorem every_prefix_bounded (requests : List Counter.Requests) (state : State signature)
    (initial : (state 0).toNat ≤ 5) (length : Nat) :
    (run (requests.take length) state 0).toNat ≤ 5 := by
  rw [history_refines]
  exact CounterReference.run_bounded _ _ initial

theorem initial_bounded : (initialState 0).toNat ≤ 5 := by decide

end Counter3

namespace Slot8

abbrev signature : Signature :=
  { nr := 2, ni := 3, regWidth := fun r => match r.val with | 0 => 1 | _ => 8
    inputType := fun i => match i.val with | 0 => .bits 1 | 1 => .bits 8 | _ => .bits 1 }
def initialState : State signature := fun _ => 0
def consume : RuleDef signature :=
  { guard := .and (.eq (.input 2) (.bitsLit 1)) (.eq (.reg 0) (.bitsLit 1))
    body := .seq (.assign 0 (.bitsLit 0)) .skip }
def enqueue : RuleDef signature :=
  { guard := .and (.eq (.input 0) (.bitsLit 1)) (.not (.eq (.reg 0) (.bitsLit 1)))
    body := .seq (.assign 1 (.input 1)) (.seq (.assign 0 (.bitsLit 1)) .skip) }
def rules := [consume, enqueue]
def occupied : Expr signature .bool := .eq (.reg 0) (.bitsLit 1)
def ready : Expr signature .bool :=
  .not (.and (.not (.not occupied)) (.not (.eq (.input 2) (.bitsLit 1))))
def outputExpressions : List (Output signature) :=
  [⟨10, .concat (.bit ready) (.concat (.reg 0) (.ite occupied (.reg 1) (.bitsLit 0)))⟩]

def inputs (request : Requests) : Inputs signature := fun i =>
  match i with
  | ⟨0, _⟩ => BitVec.ofBool request.put
  | ⟨1, _⟩ => request.data
  | ⟨2, _⟩ => BitVec.ofBool request.take
  | ⟨n + 3, h⟩ => False.elim (by change n + 3 < 3 at h; omega)

def decode (input : Inputs signature) : Requests :=
  ⟨(show BitVec 1 from input 0) == (1 : BitVec 1), input 1,
    (show BitVec 1 from input 2) == (1 : BitVec 1)⟩

theorem inputs_decode (input : Inputs signature) : inputs (decode input) = input := by
  funext i
  rcases i with ⟨i, bound⟩
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by change i < 3 at bound; omega
  rcases cases with rfl | rfl | rfl
  · exact bit_roundtrip _
  · rfl
  · exact bit_roundtrip _

def state (occupied : BitVec 1) (stored : Payload) : State signature := fun r =>
  match r with
  | ⟨0, _⟩ => occupied
  | ⟨1, _⟩ => stored
  | ⟨n + 2, h⟩ => False.elim (by change n + 2 < 2 at h; omega)

theorem state_eta (s : State signature) : state (s 0) (s 1) = s := by
  funext r
  rcases r with ⟨r, bound⟩
  have cases : r = 0 ∨ r = 1 := by change r < 2 at bound; omega
  rcases cases with rfl | rfl <;> rfl

def project (s : State signature) : List Payload := if s 0 == 1 then [s 1] else []

private theorem one_bit_cases (value : BitVec 1) : value = 0 ∨ value = 1 := by
  have bound := value.isLt
  have cases : value.toNat = 0 ∨ value.toNat = 1 := by omega
  rcases cases with zero | one
  · left; exact BitVec.eq_of_toNat_eq zero
  · right; exact BitVec.eq_of_toNat_eq one

theorem cycle_refines (request : Requests) (s : State signature) :
    project (cycle rules (inputs request) s) = Queue.step 1 request (project s) := by
  rw [← state_eta s]
  rcases one_bit_cases (s 0) with empty | full
  all_goals
    rcases request with ⟨put, data, take⟩
    cases put <;> cases take
    all_goals first | rw [empty]; rfl | rw [full]; rfl

theorem project_bounded (s : State signature) : (project s).length ≤ 1 := by
  unfold project
  split <;> simp

theorem initial_empty : project initialState = [] := rfl

theorem observation_correct (request : Requests) (s : State signature) :
    evalExpr (outputExpressions[0]'(by decide)).expression (inputs request) s =
      Queue.observation 1 request (project s) := by
  rw [← state_eta s]
  rcases one_bit_cases (s 0) with empty | full
  all_goals
    rcases request with ⟨put, data, take⟩
    cases put <;> cases take
    all_goals first | rw [empty] | rw [full]
    all_goals cbv

theorem history_refines (requests : List Requests) (s : State signature) :
    project (runRequests rules inputs requests s) = Queue.run 1 requests (project s) := by
  induction requests generalizing s with
  | nil => rfl
  | cons request rest ih =>
    rw [runRequests_cons, ih, cycle_refines]
    rfl

theorem every_prefix_bounded (requests : List Requests) (s : State signature) (length : Nat) :
    (project (runRequests rules inputs (requests.take length) s)).length ≤ 1 :=
  project_bounded _

end Slot8

namespace Fifo2x8

abbrev signature : Signature :=
  { nr := 3, ni := 3, regWidth := fun r => match r.val with | 0 => 2 | 1 => 8 | _ => 8
    inputType := fun i => match i.val with | 0 => .bits 1 | 1 => .bits 8 | _ => .bits 1 }
def initialState : State signature := fun _ => 0
def consume : RuleDef signature :=
  { guard := .and (.eq (.input 2) (.bitsLit 1)) (.ult (.bitsLit 0) (.reg 0))
    body := .seq (.assign 1 (.reg 2)) (.seq (.assign 0 (.sub (.reg 0) (.bitsLit 1))) .skip) }
def enqueue_tail : RuleDef signature :=
  { guard := .and (.eq (.input 0) (.bitsLit 1)) (.eq (.reg 0) (.bitsLit 1))
    body := .seq (.assign 2 (.input 1)) (.seq (.assign 0 (.add (.reg 0) (.bitsLit 1))) .skip) }
def enqueue_head : RuleDef signature :=
  { guard := .and (.eq (.input 0) (.bitsLit 1)) (.eq (.reg 0) (.bitsLit 0))
    body := .seq (.assign 1 (.input 1)) (.seq (.assign 0 (.add (.reg 0) (.bitsLit 1))) .skip) }
def rules := [consume, enqueue_tail, enqueue_head]
def valid : Expr signature .bool := .ult (.bitsLit 0) (.reg 0)
def ready : Expr signature .bool :=
  .not (.and (.not (.ult (.reg 0) (.bitsLit 2)))
    (.not (.and (.eq (.input 2) (.bitsLit 1)) valid)))
def outputExpressions : List (Output signature) :=
  [⟨10, .concat (.bit ready) (.concat (.bit valid) (.ite valid (.reg 1) (.bitsLit 0)))⟩]
def inputs (request : Requests) : Inputs signature := Slot8.inputs request

def decode (input : Inputs signature) : Requests := Slot8.decode input
theorem inputs_decode (input : Inputs signature) : inputs (decode input) = input :=
  Slot8.inputs_decode input

def state (count : BitVec 2) (head tail : Payload) : State signature := fun r =>
  match r with
  | ⟨0, _⟩ => count
  | ⟨1, _⟩ => head
  | ⟨2, _⟩ => tail
  | ⟨n + 3, h⟩ => False.elim (by change n + 3 < 3 at h; omega)

theorem state_eta (s : State signature) : state (s 0) (s 1) (s 2) = s := by
  funext r
  rcases r with ⟨r, bound⟩
  have cases : r = 0 ∨ r = 1 ∨ r = 2 := by change r < 3 at bound; omega
  rcases cases with rfl | rfl | rfl <;> rfl

def invariant (s : State signature) : Prop := (s 0).toNat ≤ 2
def project (s : State signature) : List Payload :=
  if s 0 == 0 then [] else if s 0 == 1 then [s 1] else [s 1, s 2]

private theorem count_cases (value : BitVec 2) (bound : value.toNat ≤ 2) :
    value = 0 ∨ value = 1 ∨ value = 2 := by
  have cases : value.toNat = 0 ∨ value.toNat = 1 ∨ value.toNat = 2 := by omega
  rcases cases with zero | one | two
  · left; exact BitVec.eq_of_toNat_eq zero
  · right; left; exact BitVec.eq_of_toNat_eq one
  · right; right; exact BitVec.eq_of_toNat_eq two

theorem rule_invariant_contract (rule : RuleDef signature) (member : rule ∈ rules) :
    Contracts.RuleContract (fun _ s => invariant s) (fun _ _ s => invariant s) rule := by
  intro input s initial
  rw [← inputs_decode input, ← state_eta s]
  rcases count_cases (s 0) initial with zero | one | two
  all_goals
    rcases (decode input) with ⟨put, data, take⟩
    cases put <;> cases take
    all_goals simp [rules] at member
    all_goals rcases member with rfl | rfl | rfl
    all_goals first | rw [zero] | rw [one] | rw [two]
    all_goals cbv

theorem rule_locally_preserves (rule : RuleDef signature) (member : rule ∈ rules) :
    LocallyPreserves invariant rule :=
  (Contracts.invariant_contract_iff invariant rule).2 (rule_invariant_contract rule member)

theorem enqueue_phase_refines (request : Requests) (s : State signature) (initial : invariant s) :
    project (cycle [enqueue_tail, enqueue_head] (inputs request) s) =
      Queue.push 2 request (project s) := by
  rw [← state_eta s]
  rcases count_cases (s 0) initial with zero | one | two
  all_goals
    rcases request with ⟨put, data, take⟩
    cases put
    all_goals first | rw [zero] | rw [one] | rw [two]
    all_goals rfl

theorem cycle_refines (request : Requests) (s : State signature) (initial : invariant s) :
    project (cycle rules (inputs request) s) = Queue.step 2 request (project s) := by
  rw [← state_eta s]
  rcases count_cases (s 0) initial with zero | one | two
  all_goals
    rcases request with ⟨put, data, take⟩
    cases put <;> cases take
    all_goals first | rw [zero] | rw [one] | rw [two]
    all_goals cbv

theorem cycle_preserves (request : Requests) (s : State signature) (initial : invariant s) :
    invariant (cycle rules (inputs request) s) := by
  apply RuleSemantics.schedule_preserves invariant _ _ (inputs request) s initial
  intro interpreted member
  rcases List.mem_map.mp member with ⟨rule, ruleMember, rfl⟩
  exact invariant_transfer invariant rule (rule_locally_preserves rule ruleMember)

theorem project_length (s : State signature) (initial : invariant s) :
    (project s).length = (s 0).toNat := by
  rcases count_cases (s 0) initial with zero | one | two
  all_goals unfold project; first | rw [zero]; rfl | rw [one]; rfl | rw [two]; rfl

theorem initial_valid : invariant initialState ∧ project initialState = [] := by
  constructor
  · change 0 ≤ 2
    decide
  · rfl

theorem observation_correct (request : Requests) (s : State signature) (initial : invariant s) :
    evalExpr (outputExpressions[0]'(by decide)).expression (inputs request) s =
      Queue.observation 2 request (project s) := by
  rw [← state_eta s]
  rcases count_cases (s 0) initial with zero | one | two
  all_goals
    rcases request with ⟨put, data, take⟩
    cases put <;> cases take
    all_goals first | rw [zero] | rw [one] | rw [two]
    all_goals cbv

theorem history_refines (requests : List Requests) (s : State signature) (initial : invariant s) :
    project (runRequests rules inputs requests s) = Queue.run 2 requests (project s) := by
  induction requests generalizing s with
  | nil => rfl
  | cons request rest ih =>
    rw [runRequests_cons, ih _ (cycle_preserves request s initial), cycle_refines request s initial]
    rfl

theorem history_preserves (requests : List Requests) (s : State signature) (initial : invariant s) :
    invariant (runRequests rules inputs requests s) := by
  induction requests generalizing s with
  | nil => exact initial
  | cons request rest ih => exact ih _ (cycle_preserves request s initial)

theorem every_prefix_bounded (requests : List Requests) (s : State signature)
    (initial : invariant s) (length : Nat) :
    (project (runRequests rules inputs (requests.take length) s)).length ≤ 2 := by
  have preserved := history_preserves (requests.take length) s initial
  rw [project_length _ preserved]
  exact preserved

end Fifo2x8

end RuleSemantics.Library
