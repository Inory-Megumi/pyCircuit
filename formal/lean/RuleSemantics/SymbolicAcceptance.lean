import RuleSemantics.Symbolic
import RuleSemantics.SyntaxAcceptance

/-! Independent literal checks reuse closed ASTs, without a second symbolic compiler. -/

namespace RuleSemantics.SymbolicAcceptance

open SyntaxAcceptance

theorem heterogeneous_forwarding :
    let final := Symbolic.evalBank (Symbolic.nextState [forwarded]) inputs (pairState 7 31)
    final 0 = 2 ∧ final 1 = 4 := by
  decide

theorem late_require_rolls_back :
    let final := Symbolic.evalBank (Symbolic.nextState [updateThenReject]) inputs (pairState 5 12)
    final 0 = 5 ∧ final 1 = 12 := by
  decide

theorem separate_root_rejection_holds_predecessor :
    let final := Symbolic.evalBank (Symbolic.nextState [updateBoth, requireBelowSix])
      inputs (pairState 5 12)
    final 0 = 6 ∧ final 1 = 13 := by
  decide

end RuleSemantics.SymbolicAcceptance
