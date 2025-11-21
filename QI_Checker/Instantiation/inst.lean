import QI_Checker.IR.TermType
import QI_Checker.IR.Term
import QI_Checker.IR.Op
import QI_Checker.Instantiation.Subst

namespace IR.Term

def inst_step (inst_term: Term) (target: Term) : Term :=
  let sb := Term.toSb inst_term
  match target with
  | .prim p => .prim p
  | .var v => .var v
  | .const c => .const c
  | .app op args => .app op (List.map (inst_step inst_term) args)
  | .quant _ _ body => body.subst sb


def inst (inst_terms: List Term) (target: Term): Term :=
  match inst_terms with
  | .nil => target
  | s :: ls  =>
    let new_target := inst_step s target
    inst ls new_target
