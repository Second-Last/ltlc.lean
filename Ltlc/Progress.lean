import Mathlib

import Ltlc.Terms
import Ltlc.Types 
import Ltlc.Context

import Ltlc.Step
import Ltlc.Typing

import Ltlc.Utils

-- For AssocList
open Lean

def IsValue (t : LtlcTerm) : Prop
  := ∃x, ∃α, ∃e, t = LtlcTerm.lam x α e

theorem progress
  (t_is_τ : HasType AssocList.nil t τ)
  : (∃t', Step t t') ∨ IsValue t :=
  by 
    match t_is_τ with 
    | @HasType.lam _ x α β e x_fresh e_is_β_with_α => 
        apply Or.inr 
        apply Exists.intro x
        apply Exists.intro α 
        apply Exists.intro e 
        trivial
    | @HasType.app _ Γ₁ Γ₂ t u α β t_is_fn u_is_α is_append => 
        apply Or.inl 
        have ⟨Γ₁_is_nil, Γ₂_is_nil⟩ : Γ₁ = .nil ∧ Γ₂ = .nil := 
          by exact nil_append_nil_nil is_append
        rw [Γ₁_is_nil] at t_is_fn
        rw [Γ₂_is_nil] at u_is_α
        match progress t_is_fn with
        | .inl ⟨t', t_to_t'⟩ => 
            apply Exists.intro (t'.app u)
            exact Step.app_left t_to_t'
        | .inr ⟨y, ⟨γ, ⟨d, issame⟩⟩⟩ =>
            match progress u_is_α with 
            | .inl ⟨u', u_to_u'⟩ =>
                apply Exists.intro (t.app u')
                exact Step.app_right u_to_u'
            | .inr ucantstep => 
                rw [issame]
                apply Exists.intro ([y // u] d)
                exact Step.app_lam
