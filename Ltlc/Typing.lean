import Mathlib

import Ltlc.Terms
import Ltlc.Types
import Ltlc.Context

inductive HasType : Context → LtlcTerm → LtlcType → Prop
  | var {x τ} : HasType (.cons x τ .nil) (.var x) τ
  | lam 
    {Γ x α β body}
    (x_fresh : ¬Bound x Γ)
    (v_hastype : HasType (.cons x α Γ) body β)
    : HasType Γ (LtlcTerm.lam x α body) (.arrow α β)
  | app 
    {Γ₁ Γ₂ t u α β}
    (t_is_fn : HasType Γ₁ t (.arrow α β))
    (u_is_α : HasType Γ₂ u α)
    (is_append : Γ ≈ Γ₁ ++ Γ₂)
    : HasType Γ (.app t u) β
