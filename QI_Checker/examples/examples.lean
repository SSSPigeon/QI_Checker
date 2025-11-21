import QI_Checker.IR.TermType
import QI_Checker.IR.Term
import QI_Checker.IR.Op
import QI_Checker.Instantiation.Inst

open IR IR.Term

-- constant c
def c : UF :=
  {
    id := "c",
    args := [],
    out := .prim .bool
  }

-- unary function f
def f : UF :=
  {
    id := "f",
    args := [.prim .bool],
    out := .prim .bool
  }

-- ex1 := ∀ x. x
abbrev ex1 := Term.quant .all (TermType.prim .bool) (.var 0)
#eval ex1.mkName


-- ex2 := ∀ x. ∀ y. y = x
abbrev ex2 := Term.quant .all (TermType.prim .bool) (Term.quant .all (TermType.prim .bool) (.app Op.eq [(.var 0), (.var 1)]))
#eval ex2.mkName

-- ∀ x. ∀ y. y = x [x ↦ true] =>
-- ∀ y. y = true
#eval (inst [.prim (.bool true)] ex2).mkName

-- ∀ x. ∀ y. y = x [x ↦ true, y ↦ false] =>
-- false = true
#eval (inst [.prim (.bool true), .prim (.bool false)] ex2).mkName


-- ex3 := ∀ x. c ∧ ∀ y. y = x
abbrev ex3 :=
  Term.quant .all (TermType.prim .bool)
    (Term.app Op.and
      [(.app (Op.uf c) []),
       Term.quant .all (TermType.prim .bool)
        (.app Op.eq [(.var 0), (.var 1)])])

#eval ex3.mkName

-- ∀ x. c ∧ ∀ y. y = x [x ↦ true, y ↦ false] =>
-- c ∧ false = true
#eval (inst [.prim (.bool true), .prim (.bool false)] ex3).mkName

-- ∀ x. c ∧ ∀ y. y = x [x ↦ c, y ↦ false] =>
-- c ∧ false = c
#eval (inst [.app (Op.uf c) [], .prim (.bool false)] ex3).mkName

-- ∃ x. f(x) ∧ ∀ y. y → x
abbrev ex4 :=
  Term.quant .exist (TermType.prim .bool)
    (Term.app Op.and
      [(.app (Op.uf f) [(.var 0)]),
       Term.quant .all (TermType.prim .bool)
        (.app Op.implies [(.var 0), (.var 1)])])

#eval ex4.mkName

-- ∃ x. f(x) ∧ ∀ y. y → x [x ↦ c, y ↦ false] =>
-- f(c) ∧ false → c
#eval (inst [.app (Op.uf c) [], .prim (.bool false)] ex4).mkName
