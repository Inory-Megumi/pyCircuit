import RuleSemantics.Library

/-! Independent contract/footprint examples and an ordered FIFO replacement law. -/

namespace RuleSemantics.LibraryAcceptance

open Syntax

abbrev signature := Library.Slot8.signature

def sampleInputs := Library.Slot8.inputs ⟨false, 0, false⟩

def narrow : RuleDef signature where
  guard := .eq (.reg 0) (.bitsLit 0)
  body := .assign 0 (.add (.reg 0) (.bitsLit 1))

def wide : RuleDef signature where
  guard := .eq (.reg 1) (.bitsLit 0)
  body := .assign 1 (.add (.reg 1) (.bitsLit 1))

theorem distinct_fields_independent : Contracts.Independent narrow wide := by
  simp [Contracts.Independent, Contracts.Disjoint, Contracts.writesRule, Contracts.readsRule,
    Contracts.writesCommand, Contracts.readsCommand, Contracts.readsExpr, narrow, wide]

theorem narrow_frame_contract :
    Contracts.RuleContract (fun _ _ => True)
      (fun _ before after => after 1 = before 1) narrow := by
  intro input before _
  exact Contracts.rule_frame narrow input before 1 (by decide)

theorem independent_orders_and_snapshot_agree (input : Inputs signature)
    (before : State signature) :
    runSchedule [interpretRule narrow, interpretRule wide] input before =
      runSchedule [interpretRule wide, interpretRule narrow] input before ∧
    (runSchedule [interpretRule narrow, interpretRule wide] input before).1 =
      Contracts.snapshotMerge narrow wide input before := by
  exact ⟨Contracts.commute_of_independent narrow wide distinct_fields_independent input before,
    Contracts.snapshot_merge_of_independent narrow wide distinct_fields_independent input before⟩

def guardDependsOnNarrow : RuleDef signature where
  guard := .eq (.reg 0) (.bitsLit 1)
  body := .assign 1 (.bitsLit 7)

/-- Disjoint writes alone do not justify reordering a guard-dependent successor. -/
theorem guard_dependency_changes_order :
    ¬ Contracts.Independent narrow guardDependsOnNarrow ∧
    (runSchedule [interpretRule narrow, interpretRule guardDependsOnNarrow]
      sampleInputs Library.Slot8.initialState).1 1 = 7 ∧
    (runSchedule [interpretRule guardDependsOnNarrow, interpretRule narrow]
      sampleInputs Library.Slot8.initialState).1 1 = 0 := by
  constructor
  · simp [Contracts.Independent, Contracts.Disjoint, Contracts.writesRule, Contracts.readsRule,
      Contracts.writesCommand, Contracts.readsCommand, Contracts.readsExpr,
      narrow, guardDependsOnNarrow]
  · constructor <;> decide

/-- Full replacement consumes the old head and retains old tail before new data. -/
theorem fifo_full_replacement (head tail data : Library.Payload) :
    Library.Fifo2x8.project
      (Library.cycle Library.Fifo2x8.rules (Library.Fifo2x8.inputs ⟨true, data, true⟩)
        (Library.Fifo2x8.state 2 head tail)) = [tail, data] := by
  rw [Library.Fifo2x8.cycle_refines _ _ (by change (2 : BitVec 2).toNat ≤ 2; decide)]
  change Library.Queue.step 2 ⟨true, data, true⟩ [head, tail] = [tail, data]
  rfl

end RuleSemantics.LibraryAcceptance
