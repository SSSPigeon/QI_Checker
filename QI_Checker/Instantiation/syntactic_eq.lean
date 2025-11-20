import QI_Checker.IR.TermType
import QI_Checker.IR.Term
import QI_Checker.IR.Op

open IR

def syntactic_eq_term (t₁ t₂: Term): Bool :=
  match t₁, t₂ with
  | .prim (.bool b₁), .prim (.bool b₂) => b₁ = b₂
  | .var v₁, .var v₂ => v₁ = v₂
  | .const c₁, .const c₂ => c₁ = c₂
  | .app op₁ args₁, .app op₂ args₂ => op₁ = op₂ ∧ args₁ = args₂
  | .quant q₁ args₁ body₁, .quant q₂ args₂ body₂ => q₁ = q₂ ∧ args₁ = args₂ ∧ body₁ = body₂
  | _, _ => false
