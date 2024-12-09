import Mathlib
import Ltlc.Utils

open Lean
open Mathlib
/- open Batteries -/

inductive LtlcType
  | base : LtlcType -- base type
  | arrow : LtlcType → LtlcType → LtlcType -- arrows/functions
  | prod : LtlcType → LtlcType → LtlcType -- (tensor) products
  | sum : LtlcType → LtlcType → LtlcType -- sum types
  deriving Repr, BEq

inductive LtlcTerm 
  | var : String → LtlcTerm
  | lam : String → LtlcType → LtlcTerm → LtlcTerm
  | app : LtlcTerm → LtlcTerm → LtlcTerm
  | left : LtlcTerm → LtlcTerm 
  | right : LtlcTerm → LtlcTerm 
  | both : LtlcTerm → LtlcTerm → LtlcTerm
  | case : LtlcTerm → String → LtlcTerm → String → LtlcTerm → LtlcTerm
  deriving Repr, BEq

def Context := AssocList String LtlcType

instance : Membership String Context where
  mem l x := l.contains x = true

instance : Append Context where
  append x y := AssocList.foldl (λ l x t => l.insert x t) y x

inductive HasType : Context → LtlcTerm → LtlcType → Prop
  | var {x τ} : HasType (AssocList.empty.insert x τ) (.var x) τ
  | lam 
    {Γ x α β body}
    (x_fresh : x ∉ Γ)
    (v_hastype : HasType (Γ.insert x t) body β)
    : HasType Γ (LtlcTerm.lam x α body) (.arrow α β)
  | app 
    {Γ₁ Γ₂ t u α β}
    (t_is_fn : HasType Γ₁ t (.arrow α β))
    (u_is_n : HasType Γ₂ u α)
    : HasType (Γ₁ ++ Γ₂) (.app t u) β
  | both 
    {Γ₁ Γ₂ x y τ₁ τ₂}
    (x_is_τ₁ : HasType Γ₁ x τ₁)
    (y_is_τ₂ : HasType Γ₂ y τ₂)
    : HasType (Γ₁ ++ Γ₂) (.both x y) (.prod τ₁ τ₂)
  | inl
    {Γ t τ₁ τ₂}
    (t_is_τ₁ : HasType Γ t τ₁)
    : HasType Γ (.left t) (.sum τ₁ τ₂)
  | inr
    {Γ t τ₁ τ₂}
    (t_is_τ₁ : HasType Γ t τ₂)
    : HasType Γ (.right t) (.sum τ₁ τ₂)
  | case 
    {Γ₁ Γ₂ t τ₁ τ₂ x₁ x₂ body₁ body₂ α}
    (ht : HasType Γ₁ t (.sum τ₁ τ₂))
    (hl : HasType (Γ₂.insert x₁ τ₁) body₁ α)
    (hr : HasType (Γ₂.insert x₂ τ₂) body₂ α)
    (x₁_fresh : x₁ ∉ Γ₂)
    (x₂_fresh : x₂ ∉ Γ₂)
    : HasType (Γ₁ ++ Γ₂) (.case t x₁ body₁ x₂ body₂) α
