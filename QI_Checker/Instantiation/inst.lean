import QI_Checker.IR.TermType
import QI_Checker.IR.Term
import QI_Checker.IR.Op
import QI_Checker.Instantiation.Subst

namespace IR.Term

def inst_step (inst_term: Term) (target: Term) : Term :=
  let sb := toSb inst_term
  match target with
  | .prim p => .prim p
  | .var v => .var v
  | .const c => .const c
  | .app op args => .app op (List.map (inst_step inst_term) args)
  | .quant _ _ body => body.subst sb

#eval (inst_step (.prim (.bool true)) ex2).mkName

def inst (inst_terms: List Term) (target: Term): Term :=
  match inst_terms with
  | .nil => target
  | s :: ls  =>
    let new_target := inst_step s target
    inst ls new_target

def uf : UF :=
  {
    id := "uf",
    args := [],
    out := .prim .bool
  }

#eval (Term.quant .all (TermType.prim .bool) (.var 0)).mkName

abbrev ex2 :=  Term.quant .all (TermType.prim .bool) (Term.quant .all (TermType.prim .bool) (.app Op.eq [(.var 0), (.var 1)]))
#eval ex2.mkName

abbrev ex3 :=  Term.quant .all (TermType.prim .bool) (.app Op.eq [(.var 0), (.var 1)])
#eval ex3.mkName

abbrev ex4 :=
  Term.quant .all (TermType.prim .bool)
    (Term.app Op.and
      [(.app (Op.uf uf) []),
       Term.quant .all (TermType.prim .bool)
        (.app Op.eq [(.var 0), (.var 1)])])

#eval ex4.mkName




#eval (inst_step (.prim (.bool true)) ex2).mkName

#eval (inst [.prim (.bool true)] ex2).mkName
#eval (inst [.prim (.bool true), .prim (.bool false)] ex2).mkName

#eval (inst [.prim (.bool true), .prim (.bool false)] ex4).mkName
