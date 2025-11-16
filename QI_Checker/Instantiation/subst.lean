import QI_Checker.IR.TermType
import QI_Checker.IR.Term
import QI_Checker.IR.Op

open IR

/-- Append an element to a substitution or a renaming.
```
Δ ⊢ σ : Γ  Γ ⊢ A  Δ ⊢ t : A[σ]
------------------------------
Δ ⊢ σ.t : Γ.A
``` -/
def snoc.{u} {X : Sort u} (σ : Nat → X) (x : X) : Nat → X
  | 0   => x
  | n+1 => σ n

@[simp]
theorem snoc_zero {X} (σ : Nat → X) (x : X) : snoc σ x 0 = x := rfl

@[simp]
theorem snoc_succ {X} (σ : Nat → X) (x : X) (n) : snoc σ x (n + 1) = σ n := rfl

/-! ## Renaming -/


/-- Lift a renaming under a binder 1 time. See `up`. -/
def upr (ξ : Nat → Nat) : Nat → Nat :=
  snoc (fun i => ξ i + 1) 0


@[simp]
theorem upr_id : upr id = id := by
  ext ⟨⟩ <;> dsimp [upr, snoc]

/-- Rename the de Bruijn indices in an expression. -/
def rename (ξ : Nat → Nat) : Term → Term :=
  sorry

/-! ## Substitution -/

/-- Lift a substitution under a binder.
```
Δ ⊢ σ : Γ  Γ ⊢ A
------------------------
Δ.A[σ] ⊢ (↑≫σ).v₀ : Γ.A
```

Warning: don't unfold this definition! Use `up_eq_snoc` instead. -/
@[irreducible]
def up (σ : Nat → Term) : Nat → Term :=
  snoc (rename Nat.succ ∘ σ) (.var 0)


@[simp]
theorem up_var : up Term.var = Term.var := by
  ext ⟨⟩ <;> (unfold up; dsimp [snoc, rename]); sorry

/-- Apply a substitution to a term. -/
def subst (σ : Nat → Term) : Term → Term := sorry


@[simp]
theorem subst_bvar: subst Term.var = id := by sorry
  --ext t; dsimp; induction t <;> grind [subst, up_bvar]

@[simp]
theorem subst_snoc_zero (σ : Nat → Term) (t : Term) : subst (snoc σ t) (.var 0) = t := by
  dsimp [subst, snoc]; sorry

/-- Turn a renaming into a substitution. -/
def ofRen (ξ : Nat → Nat) : Nat → Term :=
  fun i => Term.var (ξ i)

@[simp]
theorem ofRen_id : ofRen id = Term.var := rfl

theorem ofRen_upr: ofRen (upr ξ) = up (ofRen ξ) := by
  ext ⟨⟩ <;> simp [ofRen, upr, up, snoc, rename]; sorry

theorem rename_eq_subst_ofRen (ξ : Nat → Nat) : rename ξ = subst (ofRen ξ) := by sorry
  -- ext t
  -- induction t generalizing ξ <;> dsimp [rename, subst]
  -- case bvar => simp [ofRen]
  -- all_goals grind [ofRen_upr]

/-- Compose two substitutions.
```
Θ ⊢ σ : Δ  Δ ⊢ τ : Γ
--------------------
Θ ⊢ σ≫τ : Γ
``` -/
def comp (σ τ : Nat → Term) : Nat → Term :=
  subst σ ∘ τ

@[simp]
theorem bvar_comp (σ : Nat → Term) : comp Term.var σ = σ := by
  ext i; simp [comp]

@[simp]
theorem comp_bvar (σ : Nat → Term) : comp σ Term.var = σ := by
  ext i; simp [comp, subst]; sorry

theorem up_comp_ren_sb (ξ : Nat → Nat) (σ : Nat → Term) :
    up (σ ∘ ξ) = up σ ∘ upr ξ := by
  ext ⟨⟩ <;> (unfold up; dsimp [snoc, upr])
