import Mathlib
import Ltlc.Utils

open Lean
open Mathlib
/- open Batteries -/

inductive LtlcType
  | base : LtlcType -- base type
  | arrow : LtlcType → LtlcType → LtlcType -- arrows/functions
  deriving Repr, BEq

inductive LtlcTerm 
  | var : String → LtlcTerm
  | lam : String → LtlcType → LtlcTerm → LtlcTerm
  | app : LtlcTerm → LtlcTerm → LtlcTerm
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
    (v_hastype : HasType (Γ.insert x α) body β)
    : HasType Γ (LtlcTerm.lam x α body) (.arrow α β)
  | app 
    {Γ₁ Γ₂ t u α β}
    (t_is_fn : HasType Γ₁ t (.arrow α β))
    (u_is_α : HasType Γ₂ u α)
    : HasType (Γ₁ ++ Γ₂) (.app t u) β

def subst (x : String) (e : LtlcTerm) (a : LtlcTerm) : LtlcTerm := 
  match e with 
  | .var y => if y == x then a else .var y
  | .lam y α d => if y == x then .lam y α d else .lam y α (subst x d a)
  | .app f u => .app (subst x f a) (subst x u a)

notation  "["x" // " a"] "e => subst x e a

inductive Step : LtlcTerm → LtlcTerm → Prop 
  | app_lam {x α e a} : Step (.app (.lam x α e) a) ([x // a] e)
  | app_left {f₁ f₂ e} 
    : Step f₁ f₂ → Step (.app f₁ e) (.app f₂ e)
  | app_right {f e₁ e₂}
    : Step e₁ e₂ → Step (.app f e₁) (.app f e₂)

theorem subst_preserves_type {Γ₁ Γ₂ x α β e a} 
  : HasType (Γ₁.insert x α) e β →
    HasType Γ₂ a α →
    HasType (Γ₁ ++ Γ₂) ([x // a] e) β := sorry

theorem preservation {Γ τ e₁ e₂}
  (e₁_is_τ : HasType Γ e₁ τ)
  (e₁_steps_e₂ : Step e₁ e₂)
  : HasType Γ e₂ τ := 
    match e₁_steps_e₂ with 
    | Step.app_left f₁_steps_f₂ => 
        match e₁_is_τ with 
        | HasType.app f₁_is_fn e_is_ty => 
            HasType.app (preservation f₁_is_fn f₁_steps_f₂) e_is_ty
    | Step.app_right u₁_steps_u₂ =>
        match e₁_is_τ with 
        | HasType.app f_is_fn u₁_is_ty => 
            HasType.app f_is_fn (preservation u₁_is_ty u₁_steps_u₂)
    | @Step.app_lam x α e a => 
        match e₁_is_τ with 
        | @HasType.app Γ₁ Γ₂ _ _ _ β f_is_fn a_is_α => 
            match f_is_fn with 
            | @HasType.lam _ _ _ _ _ x_fresh bty => 
                subst_preserves_type bty a_is_α
    
