import QI_Checker.IR.TermType
import QI_Checker.IR.Term
import QI_Checker.IR.Op

namespace IR.Term

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
def rename (ξ : Nat → Nat) : Term → Term
  | .prim p => .prim p
  | .var v => .var (ξ v)
  | .app op args => .app op (List.map (rename ξ) args)
  | .quant q bv body => .quant q bv (body.rename (upr ξ))

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
  ext ⟨⟩ <;> (unfold up; simp [snoc, rename])

/-- Apply a substitution to a term. -/
def subst (σ : Nat → Term) : Term → Term
  | .prim p => .prim p
  | .var v => σ v
  | .app op args => .app op (List.map (subst σ) args)
  | .quant q bv body => .quant q bv (body.subst (up σ))

@[simp]
theorem map_id''_mem {f : α → α} (l : List α) (h : ∀ x ∈ l, f x = x)  : List.map f l = l := by
  induction l
  all_goals grind

@[simp]
theorem subst_var: subst Term.var = id := by
  ext t; dsimp; induction t <;> simp [subst, up_var];
  all_goals grind[map_id''_mem]

@[simp]
theorem subst_snoc_zero (σ : Nat → Term) (t : Term) : subst (snoc σ t) (.var 0) = t := by
  simp [subst, snoc]

/-- Turn a renaming into a substitution. -/
def ofRen (ξ : Nat → Nat) : Nat → Term :=
  fun i => Term.var (ξ i)

@[simp]
theorem ofRen_id : ofRen id = Term.var := rfl

theorem ofRen_upr: ofRen (upr ξ) = up (ofRen ξ) := by
  ext ⟨⟩ <;> simp [ofRen, upr, up, snoc, rename]

theorem rename_eq_subst_ofRen (ξ : Nat → Nat) : rename ξ = subst (ofRen ξ) := by
  ext t
  induction t generalizing ξ <;> simp [rename, subst]
  case var => simp [ofRen]
  all_goals grind [ofRen_upr]

/-- Compose two substitutions.
```
Θ ⊢ σ : Δ  Δ ⊢ τ : Γ
--------------------
Θ ⊢ σ≫τ : Γ
``` -/
def comp (σ τ : Nat → Term) : Nat → Term :=
  subst σ ∘ τ

@[simp]
theorem var_comp (σ : Nat → Term) : comp Term.var σ = σ := by
  ext i; simp [comp]

@[simp]
theorem comp_var (σ : Nat → Term) : comp σ Term.var = σ := by
  ext i; simp [comp, subst]

theorem up_comp_ren_sb (ξ : Nat → Nat) (σ : Nat → Term) :
    up (σ ∘ ξ) = up σ ∘ upr ξ := by
  ext ⟨⟩ <;> (unfold up; dsimp [snoc, upr])

theorem rename_subst (σ ξ) (t : Term) : (t.rename ξ).subst σ = t.subst (σ ∘ ξ) := by
  induction t generalizing σ ξ
  all_goals try grind [rename, subst, up_comp_ren_sb, map_id''_mem, app.injEq, List.map_inj_left]

theorem up_comp_sb_ren (σ : Nat → Term) (ξ : Nat → Nat) :
    up (rename ξ ∘ σ) = rename (upr ξ) ∘ up σ := by
  ext ⟨⟩ <;> (unfold up; simp [snoc, rename, upr])
  conv => lhs; rw [rename_eq_subst_ofRen, rename_subst]
  conv => rhs; rw [rename_eq_subst_ofRen, rename_subst]
  rfl

theorem subst_rename (ξ σ) (t : Term) :
    (t.subst σ).rename ξ = t.subst (rename ξ ∘ σ) := by
  induction t generalizing ξ σ
  all_goals grind [subst, rename, up_comp_sb_ren, map_id''_mem, app.injEq, List.map_inj_left]

theorem up_comp (σ τ : Nat → Term) :
    up (comp σ τ) = comp (up σ) (up τ) := by
  ext ⟨⟩ <;> simp [up, comp, snoc]
  simp [subst_rename, rename_subst]; congr

theorem subst_subst (σ τ : Nat → Term) (t : Term) :
    (t.subst τ).subst σ = t.subst (comp σ τ) := by
  induction t generalizing σ τ
  case var => simp [subst, comp]
  all_goals grind [subst, up_comp, map_id''_mem, app.injEq, List.map_inj_left]

theorem comp_assoc (σ τ ρ : Nat → Term) : comp σ (comp τ ρ) = comp (comp σ τ) ρ := by
  ext i
  conv => rhs; enter [0]; unfold comp
  dsimp; rw [← subst_subst]; dsimp [comp]

theorem comp_snoc (σ τ : Nat → Term) (t : Term) :
    comp σ (snoc τ t) = snoc (comp σ τ) (t.subst σ) := by
  ext ⟨⟩ <;> dsimp [comp, snoc]


/-- The weakening substitution.
```
Γ ⊢ A
------------
Γ.A ⊢ ↑ : Γ
``` -/
def wk : Nat → Term :=
  ofRen Nat.succ

@[simp]
theorem ofRen_succ : ofRen Nat.succ = wk := rfl

theorem up_eq_snoc (σ : Nat → Term) : up σ = snoc (comp wk σ) (.var 0) := by
  ext i; unfold up comp; congr 1; ext j
  rw [rename_eq_subst_ofRen]; congr 1

@[simp]
theorem snoc_comp_wk (σ : Nat → Term) (t) : comp (snoc σ t) wk = σ := by
  ext ⟨⟩ <;> simp [comp, snoc, wk, ofRen, subst, -ofRen_succ]

@[simp]
theorem snoc_wk_zero : snoc wk (Term.var 0) = Term.var := by
  ext ⟨⟩ <;> dsimp [snoc, wk, ofRen, -ofRen_succ]

theorem snoc_comp_wk_succ (σ : Nat → Term) (n) :
    snoc (comp wk σ) (var (n + 1)) = comp wk (snoc σ (var n)) := by
  ext ⟨⟩ <;> simp [comp, snoc, wk, -ofRen_succ, subst, ofRen]

/-- A substitution that instantiates one binder.
```
Γ ⊢ t : A
--------------
Γ ⊢ id.t : Γ.A
``` -/
def toSb (t : Term) : Nat → Term :=
  snoc Term.var t

end IR.Term
