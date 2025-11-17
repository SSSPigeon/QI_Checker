import Mathlib.Data.List.Defs
import Mathlib.Data.List.Basic
import QI_Checker.IR.TermType
import QI_Checker.IR.Op

/-!
Based on Cedar's Term language.
(https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/Cedar/SymCC/Term.lean)
This file defines the Term language, a strongly and simply typed IR.
-/

namespace IR

inductive TermPrim : Type where
  | bool   : Bool → TermPrim
deriving instance Repr, Inhabited, DecidableEq for TermPrim

def TermPrim.mkName : TermPrim → String
  | .bool _   => "bool"

def TermPrim.lt : TermPrim → TermPrim → Bool
  | .bool b₁, .bool b₂         => b₁ < b₂

instance : LT TermPrim where
  lt := fun x y => TermPrim.lt x y

instance TermPrim.decLt (x y : TermPrim) : Decidable (x < y) :=
  if h : TermPrim.lt x y then isTrue h else isFalse h

inductive QuantifierKind
  | all
  | exist
deriving Repr, DecidableEq, Hashable


inductive Term : Type where
  | prim    : TermPrim → Term
  | var     : Nat → Term
  | app     : Op → (args: List Term) → Term
  | quant   : QuantifierKind → (bv: TermType) → (body: Term) → Term
deriving instance Repr, Inhabited for Term

@[induction_eliminator]
theorem Term.induct {P : Term → Prop}
  (prim : ∀t, P (.prim t))
  (var: ∀v, P (.var v))
  (app: ∀op args, (∀ t ∈ args, P t) → P (.app op args))
  (quant: ∀q args body, P body → P (.quant q args body)) :
  ∀ ty, P ty := by
  intro t
  let motive₁ := fun t => P t
  let motive₂ := fun ts => List.Forall P ts
  apply @Term.recOn (motive_1 := motive₁) (motive_2 := motive₂) <;> try assumption
  case nil => exact trivial
  all_goals grind[List.forall_iff_forall_mem]


def Term.isVar (t : Term) : Bool :=
  match t with
  | .var _ => true
  | _ => false

mutual
def Term.hasDecEq (t t' : Term) : Decidable (t = t') := by
  cases t <;> cases t' <;>
  try { apply isFalse ; intro h ; injection h }
  case prim.prim v₁ v₂ | var.var v₁ v₂ =>
    exact match decEq v₁ v₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case app.app op ts op' ts' =>
    exact match decEq op op', Term.hasListDec ts ts' with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse h₁, _ | _, isFalse h₁  =>
      isFalse (by intro h₂; simp [h₁] at h₂)
  case quant.quant qk args t qk' args' t' =>
    exact match decEq qk qk', decEq args args', Term.hasDecEq t t' with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse h₁, _, _ | _, isFalse h₁, _ | _, _, isFalse h₁ =>
      isFalse (by intro h₂; simp [h₁] at h₂)

def Term.hasListDec (ts₁ ts₂ : List Term) : Decidable (ts₁ = ts₂) :=
  match ts₁, ts₂ with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | t₁ :: tl₁, t₂ :: tl₂ =>
    match Term.hasDecEq t₁ t₂ with
    | isTrue h₁ =>
        match Term.hasListDec tl₁ tl₂ with
        | isTrue h₂ => isTrue (by subst h₁ h₂; rfl)
        | isFalse _ => isFalse (by simp; intros; assumption)
    | isFalse _ => isFalse (by simp; intros; contradiction)
end

instance : DecidableEq Term := Term.hasDecEq

def hashTerm (t: Term): UInt64 :=
  match t with
    | .prim _ => 2
    | .var _ => 3
    | .app op _ => 11 * (hash op)
    | .quant qk args _ => 13 * (hash qk) * (hash args)

instance : Hashable Term where
  hash := hashTerm

def Term.mkName : Term → String
  | .prim _     => "prim"
  | .var _      => "var"
  | .app _ _  => "app"
  | .quant .all __ _ => "all"
  | .quant .exist _ _ => "exists"


abbrev Term.bool (b : Bool) : Term := .prim (.bool b)

def TermPrim.typeOf : TermPrim → TermType
  | .bool _           => .bool


def Term.isLiteral : Term → Bool
  | .prim _
  | _                     => false

instance : Coe Bool Term where
  coe b := .prim (.bool b)

instance : Coe Nat Term where
  coe v := .var v

end IR
