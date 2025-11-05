/-!
Based on Cedar's Term language.
(https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/Cedar/SymCC/TermType.lean)
This file defines the types of Terms.
-/

namespace IR

inductive TermPrimType where
  | bool
deriving instance Repr, Inhabited, DecidableEq for TermPrimType

def TermPrimType.mkName : TermPrimType → String
  | .bool     => "bool"

inductive TermType where
  | prim (pty : TermPrimType)
  | option (ty : TermType)
  | constr (id : String) (args : List TermType)
deriving instance Repr, Inhabited for TermType

/--
Induction rule for `TermType`: the default induction tactic doesn't yet support
nested or mutual induction types.
-/
@[induction_eliminator]
theorem TermType.induct {P : TermType → Prop}
  (prim : ∀pty, P (.prim pty))
  (option : ∀ty, P ty → P (.option ty))
  (constr : ∀id args, (∀ ty ∈ args, P ty) → P (.constr id args)) :
  ∀ ty, P ty := by
  intro n
  apply TermType.rec <;> try assumption
  case nil => simp
  case cons => simp_all

def TermType.mkName : TermType → String
  | .prim _   => "prim"
  | option _ => "option"
  | .constr id _ => id

instance : Hashable TermType where
  hash := λ a => hash s!"{repr a}"

def TermType.beq : TermType → TermType → Bool
  | .prim pty₁, .prim pty₂ => pty₁ == pty₂
  | .constr id₁ args₁, .constr id₂ args₂ => id₁ == id₂ && go args₁ args₂
  | .option ty₁, .option ty₂ => TermType.beq ty₁ ty₂
  | _, _ => false
  where go : List TermType → List TermType → Bool
  | [], [] => true
  | [], _ | _, [] => false
  | a1 :: rst1, a2 :: rst2 => TermType.beq a1 a2 && go rst1 rst2

@[simp]
theorem TermType.beq_refl : TermType.beq ty ty := by
  induction ty <;> simp_all [TermType.beq]
  rename_i name args ih
  induction args
  case constr.nil => simp [TermType.beq.go]
  case constr.cons =>
    rename_i head tail ih'
    simp_all [TermType.beq.go]
  done

instance : DecidableEq TermType :=
  fun x y =>
    if h: TermType.beq x y then
      isTrue (by
                induction x generalizing y
                case prim =>
                  unfold TermType.beq at h <;> split at h <;> simp_all
                case option =>
                  unfold TermType.beq at h <;> split at h <;> simp_all
                  rename_i _ _ _ _ ty2 h1 _
                  exact h1 ty2 h
                case constr =>
                  rename_i id args ih
                  cases y <;> try simp_all [TermType.beq]
                  rename_i id' args'
                  obtain ⟨h1, h2⟩ := h
                  induction args generalizing args' <;> simp_all
                  case constr.nil =>
                    unfold TermType.beq.go at h2
                    split at h2 <;> simp_all
                  case constr.cons head tail tail_ih =>
                    unfold TermType.beq.go at h2; split at h2 <;> simp_all
                    obtain ⟨h2_1, h2_2⟩ := h2
                    obtain ⟨ih1, ih2⟩ := ih
                    rename_i _ _ _ _ a2 rst2 _
                    exact ⟨ih1 a2 h2_1, tail_ih ih2 rst2 h2_2⟩)
    else
      isFalse (by
                induction x generalizing y
                case prim =>
                  unfold TermType.beq at h; split at h <;> simp_all
                  rename_i pty _ _ _ h
                  exact fun a ↦ h pty (id (Eq.symm a))
                case option =>
                  unfold TermType.beq at h <;> split at h <;> simp_all
                  rename_i ty _ _ _ _ h2
                  exact fun a => h2 ty ty rfl (id (Eq.symm a))
                case constr =>
                  rename_i id args ih
                  cases y <;> try simp_all [TermType.beq]
                  rename_i id' args'
                  induction args generalizing args' <;> simp_all
                  case constr.nil =>
                    unfold TermType.beq.go at h
                    split at h <;> simp_all
                  case constr.cons head tail tail_ih =>
                    intro h1; subst id'; simp_all
                    obtain ⟨ih1, ih2⟩ := ih
                    cases args' <;> simp_all
                    rename_i head1 tail1; intro h_head; subst head1
                    have tail_ih' := @tail_ih tail1
                    unfold TermType.beq.go at h
                    simp at h; exact tail_ih tail1 h)

abbrev TermType.bool : TermType := .prim .bool


def TermType.isPrimType : TermType → Bool
  | .prim _ => true
  | _       => false

def TermType.isConstrType : TermType → Bool
  | .constr _ _ => true
  | _         => false

end IR
