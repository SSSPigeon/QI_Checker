import QI_Checker.IR.TermType
import QI_Checker.IR.Term
import QI_Checker.IR.Op

open IR

def syntactic_eq (t₁ t₂: Term): Option Bool :=
  match t₁, t₂ with
  | .prim (.bool b₁), .prim (.bool b₂) => some (b₁ = b₂)
  | .var v₁, .var v₂ => some (v₁.id = v₂.id ∧ v₁.ty = v₂.ty)
  -- | .app op₁ args₁ ret₁, .app op₂ args₂ ret₂ =>
  | _, _ => none
