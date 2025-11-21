import QI_Checker.IR.TermType
import QI_Checker.IR.Term
import QI_Checker.IR.Op
import QI_Checker.Instantiation.Inst

open IR IR.Term

-- ex1 := ∀ x. x
abbrev ex1 := Term.quant .all (TermType.prim .bool) (.var 0)
#eval ex1.mkName

-- ex2 := ∀ x. ∀ y. y = x
abbrev ex2 := Term.quant .all (TermType.prim .bool) (Term.quant .all (TermType.prim .bool) (.app Op.eq [(.var 0), (.var 1)]))
#eval ex2.mkName


#eval (inst_step (.prim (.bool true)) ex2).mkName

#eval (inst [.prim (.bool true)] ex2).mkName
#eval (inst [.prim (.bool true), .prim (.bool false)] ex2).mkName



def uf : UF :=
  {
    id := "uf",
    args := [],
    out := .prim .bool
  }


abbrev ex4 :=
  Term.quant .all (TermType.prim .bool)
    (Term.app Op.and
      [(.app (Op.uf uf) []),
       Term.quant .all (TermType.prim .bool)
        (.app Op.eq [(.var 0), (.var 1)])])

#eval ex4.mkName
#eval (inst [.prim (.bool true), .prim (.bool false)] ex4).mkName
