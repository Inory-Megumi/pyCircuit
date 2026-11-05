import RuleSemantics.Syntax

/-!
Pure next-state terms for the closed Rule syntax. Reads refer to cycle-entry
state; substitution threads candidate writes and each root's commit/hold choice.
The executable serializer checks construction limits before calling this layer.
-/

namespace RuleSemantics.Symbolic

open Syntax

inductive Term (signature : Signature) : ValueType → Type where
  | boolLit (value : Bool) : Term signature .bool
  | bitsLit (value : BitVec width) : Term signature (.bits width)
  | input (index : Fin signature.ni) : Term signature (signature.inputType index)
  | read (register : Fin signature.nr) : Term signature (.bits (signature.regWidth register))
  | add (left right : Term signature (.bits width)) : Term signature (.bits width)
  | sub (left right : Term signature (.bits width)) : Term signature (.bits width)
  | ult (left right : Term signature (.bits width)) : Term signature .bool
  | eq (left right : Term signature type) : Term signature .bool
  | and (left right : Term signature .bool) : Term signature .bool
  | not (value : Term signature .bool) : Term signature .bool
  | ite (condition : Term signature .bool) (yes no : Term signature type) : Term signature type

def evalTerm (term : Term signature type) (input : Inputs signature)
    (entry : State signature) : type.denote :=
  match term with
  | .boolLit value => value
  | .bitsLit value => value
  | .input index => input index
  | .read register => entry register
  | .add left right => evalTerm left input entry + evalTerm right input entry
  | .sub left right => evalTerm left input entry - evalTerm right input entry
  | .ult left right => (evalTerm left input entry).ult (evalTerm right input entry)
  | .eq left right => valueEqual _ (evalTerm left input entry) (evalTerm right input entry)
  | .and left right => evalTerm left input entry && evalTerm right input entry
  | .not value => !(evalTerm value input entry)
  | .ite condition yes no =>
    if evalTerm condition input entry then evalTerm yes input entry else evalTerm no input entry

inductive Cached : {n : Nat} → (Fin n → Type) → Type 1 where
  | nil {α : Fin 0 → Type} : Cached α
  | cons {α : Fin (n + 1) → Type} (head : α 0)
      (tail : Cached (fun index : Fin n => α index.succ)) : Cached α

def Cached.get : {n : Nat} → {α : Fin n → Type} → Cached α → (i : Fin n) → α i
  | _, _, .nil, index => Fin.elim0 index
  | _, _, .cons head tail, index => Fin.cases head (fun next => tail.get next) index

/-- The inductive result forces every entry; a function result would be eta-expanded. -/
@[noinline] def cache : {n : Nat} → (α : Fin n → Type) → ((i : Fin n) → α i) → Cached α
  | 0, _, _ => .nil
  | n + 1, α, values =>
    let head := values 0
    let tail := cache (fun index : Fin n => α index.succ) (fun index => values index.succ)
    .cons head tail

theorem cache_eq {n : Nat} (α : Fin n → Type) (values : (i : Fin n) → α i) :
    (cache α values).get = values := by
  induction n with
  | zero => funext index; exact Fin.elim0 index
  | succ n ih =>
    funext index
    refine Fin.cases ?_ (fun next => ?_) index
    · rfl
    · simp only [cache, Cached.get, Fin.cases_succ, ih]

abbrev Bank (signature : Signature) :=
  Cached (fun register : Fin signature.nr => Term signature (.bits (signature.regWidth register)))

def cacheBank (bank : (register : Fin signature.nr) →
    Term signature (.bits (signature.regWidth register))) : Bank signature := cache _ bank

@[simp] theorem cacheBank_eq (bank : (register : Fin signature.nr) →
    Term signature (.bits (signature.regWidth register))) : (cacheBank bank).get = bank :=
  cache_eq _ bank

def evalBank (bank : Bank signature) (input : Inputs signature) (entry : State signature) :
    State signature := fun register => evalTerm (bank.get register) input entry

def writeBank (bank : Bank signature) (register : Fin signature.nr)
    (value : Term signature (.bits (signature.regWidth register))) : Bank signature :=
  cacheBank (fun other => if same : register = other then same ▸ value else bank.get other)

theorem eval_writeBank (bank : Bank signature) (register : Fin signature.nr)
    (value : Term signature (.bits (signature.regWidth register)))
    (input : Inputs signature) (entry : State signature) :
    evalBank (writeBank bank register value) input entry =
      writeReg (evalBank bank input entry) register (evalTerm value input entry) := by
  funext other
  by_cases same : register = other
  · subst other; simp [evalBank, writeBank]
  · simp [evalBank, writeBank, writeReg, same]

def lowerExpr (expression : Expr signature type) (bank : Bank signature) : Term signature type :=
  match expression with
  | .boolLit value => .boolLit value
  | .bitsLit value => .bitsLit value
  | .input index => .input index
  | .reg register => bank.get register
  | .add left right => .add (lowerExpr left bank) (lowerExpr right bank)
  | .sub left right => .sub (lowerExpr left bank) (lowerExpr right bank)
  | .ult left right => .ult (lowerExpr left bank) (lowerExpr right bank)
  | .eq left right => .eq (lowerExpr left bank) (lowerExpr right bank)
  | .and left right => .and (lowerExpr left bank) (lowerExpr right bank)
  | .not value => .not (lowerExpr value bank)

theorem expression_correct (expression : Expr signature type) (bank : Bank signature)
    (input : Inputs signature) (entry : State signature) :
    evalTerm (lowerExpr expression bank) input entry =
      evalExpr expression input (evalBank bank input entry) := by
  induction expression <;> simp_all [lowerExpr, evalTerm, evalExpr, evalBank]

structure Candidate (signature : Signature) where
  accepted : Term signature .bool
  bank : Bank signature

def lowerCommand (command : Command signature) (bank : Bank signature) : Candidate signature :=
  match command with
  | .skip => ⟨.boolLit true, bank⟩
  | .assign register expression =>
    let value := lowerExpr expression bank
    ⟨.boolLit true, writeBank bank register value⟩
  | .require condition => ⟨lowerExpr condition bank, bank⟩
  | .seq first second =>
    let initial := lowerCommand first bank
    let later := lowerCommand second initial.bank
    ⟨.and initial.accepted later.accepted, later.bank⟩

/-- A rejected command has no candidate, including after speculative writes. -/
theorem command_correct (command : Command signature) (bank : Bank signature)
    (input : Inputs signature) (entry : State signature) :
    evalCommand command input (evalBank bank input entry) =
      if evalTerm (lowerCommand command bank).accepted input entry then
        some (evalBank (lowerCommand command bank).bank input entry) else none := by
  induction command generalizing bank with
  | skip => rfl
  | assign register expression =>
    simp [evalCommand, lowerCommand, evalTerm, eval_writeBank, expression_correct]
  | require condition =>
    simp [evalCommand, lowerCommand, expression_correct]
  | seq first second ihFirst ihSecond =>
    simp only [evalCommand, ihFirst, lowerCommand, evalTerm]
    by_cases initial : evalTerm (lowerCommand first bank).accepted input entry = true
    · simp only [initial, ↓reduceIte, Bool.true_and]
      exact ihSecond _
    · simp [initial]

def lowerRule (rule : RuleDef signature) (bank : Bank signature) : Bank signature :=
  let body := lowerCommand rule.body bank
  let accepted := Term.and (lowerExpr rule.guard bank) body.accepted
  cacheBank (fun register => .ite accepted (body.bank.get register) (bank.get register))

theorem rule_correct (rule : RuleDef signature) (bank : Bank signature)
    (input : Inputs signature) (entry : State signature) :
    evalBank (lowerRule rule bank) input entry =
      (runRule (interpretRule rule) input (evalBank bank input entry)).1 := by
  rw [runRule_correspondence]
  simp only [lowerRule]
  unfold runRule directRule candidate evalRule
  rw [command_correct]
  funext register
  by_cases guarded : evalExpr rule.guard input (evalBank bank input entry) = true
  · by_cases accepted : evalTerm (lowerCommand rule.body bank).accepted input entry = true
    · simp [evalBank, evalTerm, expression_correct, guarded, accepted]
    · simp [evalBank, evalTerm, expression_correct, guarded, accepted]
  · simp [evalBank, evalTerm, expression_correct, guarded]

def lowerSchedule (rules : List (RuleDef signature)) (bank : Bank signature) : Bank signature :=
  rules.foldl (fun current rule => lowerRule rule current) bank

theorem schedule_correct (rules : List (RuleDef signature)) (bank : Bank signature)
    (input : Inputs signature) (entry : State signature) :
    evalBank (lowerSchedule rules bank) input entry =
      (runSchedule (rules.map interpretRule) input (evalBank bank input entry)).1 := by
  induction rules generalizing bank with
  | nil => rfl
  | cons rule rest ih =>
    change evalBank (lowerSchedule rest (lowerRule rule bank)) input entry = _
    rw [ih, rule_correct]
    rfl

def nextState (rules : List (RuleDef signature)) : Bank signature :=
  lowerSchedule rules (cacheBank (fun register => .read register))

theorem nextState_correct (rules : List (RuleDef signature)) (input : Inputs signature)
    (entry : State signature) :
    evalBank (nextState rules) input entry =
      (runSchedule (rules.map interpretRule) input entry).1 := by
  rw [nextState, schedule_correct]
  congr 2
  funext register
  simp [evalBank, evalTerm]

end RuleSemantics.Symbolic
