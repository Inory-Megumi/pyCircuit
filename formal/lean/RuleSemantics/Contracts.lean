import RuleSemantics.Syntax

/-!
State contracts and structural independence for closed, Empty-event Rules.
Rejection holds a root's entry state. Sequential and snapshot-merge theorems
retain separate roots and do not assert commutation of nonempty event traces.
-/

namespace RuleSemantics.Contracts

open Syntax

abbrev Pre (signature : Signature) := Inputs signature → State signature → Prop
abbrev Post (signature : Signature) := Inputs signature → State signature → State signature → Prop

def step (rule : RuleDef signature) (input : Inputs signature) (state : State signature) :
    State signature := (runRule (interpretRule rule) input state).1

theorem step_direct (rule : RuleDef signature) (input : Inputs signature) (state : State signature) :
    step rule input state = (evalRule rule input state).getD state := by
  rw [step, runRule_correspondence]
  cases outcome : evalRule rule input state <;>
    simp [runRule, directRule, candidate, outcome]

theorem runRule_empty (rule : RuleDef signature) (input : Inputs signature) (state : State signature) :
    runRule (interpretRule rule) input state = (step rule input state, []) := by
  rw [runRule_correspondence, step_direct]
  cases outcome : evalRule rule input state <;>
    simp [runRule, directRule, candidate, outcome]

def RuleContract (pre : Pre signature) (post : Post signature) (rule : RuleDef signature) : Prop :=
  ∀ input before, pre input before → post input before (step rule input before)

def ScheduleContract (pre : Pre signature) (post : Post signature)
    (rules : List (RuleDef signature)) : Prop :=
  ∀ input before, pre input before →
    post input before (runSchedule (rules.map interpretRule) input before).1

theorem rule_contract_of_candidates (pre : Pre signature) (post : Post signature)
    (rule : RuleDef signature)
    (accepted : ∀ input before after, pre input before →
      evalRule rule input before = some after → post input before after)
    (held : ∀ input before, pre input before → post input before before) :
    RuleContract pre post rule := by
  intro input before initial
  rw [step_direct]
  cases outcome : evalRule rule input before with
  | none => exact held input before initial
  | some after => exact accepted input before after initial outcome

theorem schedule_cons_contract (pre : Pre signature) (firstPost : Post signature)
    (nextPre : Pre signature) (nextPost : Post signature) (rule : RuleDef signature)
    (rest : List (RuleDef signature)) (first : RuleContract pre firstPost rule)
    (next : ScheduleContract nextPre nextPost rest)
    (handoff : ∀ input before middle, pre input before → firstPost input before middle →
      nextPre input middle) :
    ScheduleContract pre (fun input before after =>
      ∃ middle, firstPost input before middle ∧ nextPost input middle after) (rule :: rest) := by
  intro input before initial
  have firstResult := first input before initial
  exact ⟨step rule input before, firstResult,
    next input _ (handoff input before _ initial firstResult)⟩

theorem invariant_contract_iff (invariant : State signature → Prop) (rule : RuleDef signature) :
    LocallyPreserves invariant rule ↔
      RuleContract (fun _ state => invariant state) (fun _ _ state => invariant state) rule := by
  constructor
  · intro safe
    exact rule_contract_of_candidates _ _ rule safe (fun _ _ initial => initial)
  · intro safe input before after initial accepted
    have result := safe input before initial
    simpa [step_direct, accepted] using result

def readsExpr : Expr signature type → List (Fin signature.nr)
  | .boolLit _ | .bitsLit _ | .input _ => []
  | .reg register => [register]
  | .add left right | .sub left right | .ult left right | .eq left right | .and left right =>
    readsExpr left ++ readsExpr right
  | .not value | .bit value => readsExpr value
  | .concat high low => readsExpr high ++ readsExpr low
  | .ite condition yes no => readsExpr condition ++ readsExpr yes ++ readsExpr no

def readsCommand : Command signature → List (Fin signature.nr)
  | .skip => []
  | .assign _ value => readsExpr value
  | .require condition => readsExpr condition
  | .seq first second => readsCommand first ++ readsCommand second

def writesCommand : Command signature → List (Fin signature.nr)
  | .skip | .require _ => []
  | .assign register _ => [register]
  | .seq first second => writesCommand first ++ writesCommand second

def readsRule (rule : RuleDef signature) := readsExpr rule.guard ++ readsCommand rule.body
def writesRule (rule : RuleDef signature) := writesCommand rule.body

def AgreeOn (registers : List (Fin signature.nr)) (left right : State signature) : Prop :=
  ∀ register ∈ registers, left register = right register

theorem agree_subset (small big : List (Fin signature.nr))
    (contained : ∀ register ∈ small, register ∈ big) (left right : State signature)
    (agree : AgreeOn big left right) : AgreeOn small left right := by
  intro register member
  exact agree register (contained register member)

theorem expression_local (expression : Expr signature type) (input : Inputs signature)
    (left right : State signature) (agree : AgreeOn (readsExpr expression) left right) :
    evalExpr expression input left = evalExpr expression input right := by
  induction expression <;>
    simp_all [readsExpr, AgreeOn, evalExpr, List.mem_append, or_imp, forall_and]

theorem command_frame (command : Command signature) (input : Inputs signature)
    (before after : State signature) (accepted : evalCommand command input before = some after)
    (register : Fin signature.nr) (outside : register ∉ writesCommand command) :
    after register = before register := by
  induction command generalizing before after with
  | skip => cases accepted; rfl
  | assign target value =>
    simp only [evalCommand, Option.some.injEq] at accepted
    subst after
    exact writeReg_other before target register _ (by simpa [writesCommand, eq_comm] using outside)
  | require condition =>
    simp only [evalCommand] at accepted
    split at accepted
    · cases accepted; rfl
    · contradiction
  | seq first second ihFirst ihSecond =>
    simp only [evalCommand] at accepted
    cases result : evalCommand first input before with
    | none => simp [result] at accepted
    | some middle =>
      simp only [result] at accepted
      have notFirst : register ∉ writesCommand first := by simp_all [writesCommand]
      have notSecond : register ∉ writesCommand second := by simp_all [writesCommand]
      exact (ihSecond middle after accepted notSecond).trans (ihFirst before middle result notFirst)

theorem rule_frame (rule : RuleDef signature) (input : Inputs signature)
    (state : State signature) (register : Fin signature.nr) (outside : register ∉ writesRule rule) :
    step rule input state register = state register := by
  rw [step_direct]
  unfold evalRule
  split
  · cases result : evalCommand rule.body input state with
    | none => rfl
    | some after => exact command_frame rule.body input state after result register outside
  · rfl

private def OutcomeAgree (scope : List (Fin signature.nr)) :
    Option (State signature) → Option (State signature) → Prop
  | none, none => True
  | some left, some right => AgreeOn scope left right
  | _, _ => False

private theorem command_local (command : Command signature) (scope : List (Fin signature.nr))
    (contained : ∀ r ∈ readsCommand command, r ∈ scope) (input : Inputs signature)
    (left right : State signature) (agree : AgreeOn scope left right) :
    OutcomeAgree scope (evalCommand command input left) (evalCommand command input right) := by
  induction command generalizing left right with
  | skip => exact agree
  | assign target value =>
    have same := expression_local value input left right (agree_subset _ _ contained _ _ agree)
    change AgreeOn scope (writeReg left target (evalExpr value input left))
      (writeReg right target (evalExpr value input right))
    rw [same]
    intro r member
    by_cases equal : target = r
    · subst r; simp
    · simpa [writeReg, equal] using agree r member
  | require condition =>
    have same := expression_local condition input left right (agree_subset _ _ contained _ _ agree)
    simp only [evalCommand, same]
    split
    · exact agree
    · trivial
  | seq first second ihFirst ihSecond =>
    have firstContained : ∀ r ∈ readsCommand first, r ∈ scope := by
      intro r h; exact contained r (by simp [readsCommand, h])
    have secondContained : ∀ r ∈ readsCommand second, r ∈ scope := by
      intro r h; exact contained r (by simp [readsCommand, h])
    have initial := ihFirst firstContained left right agree
    simp only [evalCommand]
    cases a : evalCommand first input left <;> cases b : evalCommand first input right <;>
      simp only [a, b, OutcomeAgree] at initial ⊢
    all_goals try contradiction
    exact ihSecond secondContained _ _ initial

theorem rule_local (rule : RuleDef signature) (input : Inputs signature)
    (left right : State signature) (scope : List (Fin signature.nr))
    (contained : ∀ r ∈ readsRule rule, r ∈ scope) (agree : AgreeOn scope left right) :
    AgreeOn scope (step rule input left) (step rule input right) := by
  have guardSame := expression_local rule.guard input left right
    (agree_subset _ _ (fun r h => contained r (by simp [readsRule, h])) _ _ agree)
  have bodySame := command_local rule.body scope
    (fun r h => contained r (by simp [readsRule, h])) input left right agree
  simp only [step_direct, evalRule, guardSame]
  split
  · cases a : evalCommand rule.body input left <;> cases b : evalCommand rule.body input right <;>
      simp only [a, b, OutcomeAgree] at bodySame ⊢
    all_goals first | contradiction | exact agree | exact bodySame
  · exact agree

def Disjoint {signature : Signature} (left right : List (Fin signature.nr)) : Prop :=
  ∀ r ∈ left, r ∈ right → False

def Independent (first second : RuleDef signature) : Prop :=
  Disjoint (writesRule first) (readsRule second ++ writesRule second) ∧
    Disjoint (writesRule second) (readsRule first ++ writesRule first)

private theorem stable (first second : RuleDef signature) (input : Inputs signature)
    (state : State signature)
    (independent : Disjoint (writesRule second) (readsRule first ++ writesRule first)) :
    AgreeOn (writesRule first) (step first input (step second input state)) (step first input state) := by
  apply agree_subset _ (readsRule first ++ writesRule first) (by intro r h; simp [h]) _ _
  apply rule_local first input _ _ _ (by intro r h; simp [h])
  intro r member
  exact rule_frame second input state r (fun written => independent r written member)

theorem commute_of_independent (first second : RuleDef signature)
    (independent : Independent first second) (input : Inputs signature) (state : State signature) :
    runSchedule [interpretRule first, interpretRule second] input state =
      runSchedule [interpretRule second, interpretRule first] input state := by
  simp only [runSchedule, runRule_empty]
  simp only [List.append_nil]
  congr 1
  funext r
  by_cases inFirst : r ∈ writesRule first
  · have outside : r ∉ writesRule second := by
      intro written; exact independent.1 r inFirst (by simp [written])
    rw [rule_frame second input _ r outside]
    exact (stable first second input state independent.2 r inFirst).symm
  · by_cases inSecond : r ∈ writesRule second
    · rw [rule_frame first input _ r inFirst]
      exact stable second first input state independent.1 r inSecond
    · simp only [rule_frame first input _ r inFirst, rule_frame second input _ r inSecond]

def snapshotMerge (first second : RuleDef signature) (input : Inputs signature)
    (state : State signature) : State signature :=
  fun r => if r ∈ writesRule first then step first input state r
    else if r ∈ writesRule second then step second input state r else state r

theorem snapshot_merge_of_independent (first second : RuleDef signature)
    (independent : Independent first second) (input : Inputs signature) (state : State signature) :
    (runSchedule [interpretRule first, interpretRule second] input state).1 =
      snapshotMerge first second input state := by
  change step second input (step first input state) = _
  funext r
  by_cases inFirst : r ∈ writesRule first
  · have outside : r ∉ writesRule second := by
      intro written; exact independent.1 r inFirst (by simp [written])
    simp only [snapshotMerge, inFirst, ↓reduceIte, rule_frame second input _ r outside]
  · by_cases inSecond : r ∈ writesRule second
    · simp only [snapshotMerge, inFirst, inSecond, ↓reduceIte]
      exact stable second first input state independent.1 r inSecond
    · simp [snapshotMerge, inFirst, inSecond, rule_frame]

end RuleSemantics.Contracts
