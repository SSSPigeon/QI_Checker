import QI_Checker.IR.TermType

/-!
Based on Cedar's Term language.
(https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/Cedar/SymCC/Op.lean)
This file defines the operators on Terms.
-/

namespace IR

structure TermVar where
  id : Nat        -- de Bruijn index
  ty : TermType
deriving Repr, DecidableEq, Inhabited

structure UF where
  id : String
  args : List TermVar
  out : TermType
deriving Repr, DecidableEq, Inhabited

instance : Hashable UF where
  hash := λ a => hash s!"{repr a}"

inductive Op : Type where
  ---------- SMTLib core theory of equality with uninterpreted functions (`UF`) ----------
  ---------- https://smt-lib.org/theories-Core.shtml ----------
  | not
  | and
  | or
  | xor
  | eq
  | ite
  | implies
  | distinct
  | uf : UF → Op
deriving Repr, DecidableEq, Inhabited, Hashable


def Op.mkName : Op → String
  | .not           => "not"
  | .and           => "and"
  | .or            => "or"
  | .xor           => "xor"
  | .eq            => "eq"
  | .ite           => "ite"
  | .implies       => "=>"
  | .distinct      => "distinct"
  | .uf u          => s!"{u.id}"

end IR
