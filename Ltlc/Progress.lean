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

-- lemma nil_append_is_same {Γ : Context} : AssocList.nil ++ Γ = Γ := sorry
-- 
-- lemma lem1 {Γ Γ₁ Γ₂ : Context}
--   (x_fresh : x ∉ Γ)
--   (is_append : AssocList.cons x α Γ ≈ Γ₁ ++ Γ₂)
--   : (∃Γ₃, AssocList.cons x α Γ₃ ≈ Γ₁ ∧ x ∉ Γ₂)
--     ∨ (∃Γ₃, AssocList.cons x α Γ₃ ≈ Γ₂ ∨ x ∉ Γ₁) := sorry
-- 
-- theorem extract_context {α : LtlcType} (Γ : Context) (x : String) (x_in_Γ : x ∈ Γ)
--   : ∃Γ', (.cons x α Γ') ≈ Γ := sorry
-- 
-- lemma equiv_context_replacable {Γ₁ Γ₂ : Context}
--   (t : HasType Γ₁ e α)
--   (Γ₁_equiv_Γ₂ : Γ₁ ≈ Γ₂)
--   : HasType Γ₂ e α := sorry
-- 
-- lemma cons_is_append_single {Γ : Context} {x : String} {α : LtlcType}
--   : AssocList.cons x α Γ = Γ ++ (AssocList.cons x α AssocList.nil) := rfl
-- 

-- theorem subst_lemma {Γ x α β e a} 
--   (x_fresh : x ∉ Γ)
--   (p1 : (HasType (.cons x α Γ) e β) ∨ HasType Γ e β)
--   (p2 : HasType .nil a α)
--   : HasType Γ ([x // a] e) β :=
--     match e with 
--     | .var y => 
--         by 
--           by_cases heq : y = x 
--           . simp [heq]
--             rw [heq] at p1 
--             cases p1 with 
--             | inl pwx => 
--                 cases pwx with
--                 | var => exact p2
--             | inr pwox =>
--                 cases pwox with 
--                 | var => 
--                     have x_not_fresh : x ∈ AssocList.cons x β AssocList.nil := 
--                       by
--                         simp [Membership.mem, AssocList.contains]
--                     contradiction
--           . simp [heq]
--             cases p1 with
--             | inl pwx => 
--                 cases pwx with
--                 | var => contradiction
--             | inr pwox =>
--                 cases pwox with 
--                 | var => exact HasType.var
--     | .lam z γ d =>
--         by 
--           cases p1 with
--           | inl pwx => 
--               match pwx with 
--               | @HasType.lam _ _ _ μ _ z_fresh d_hastype => 
--                   simp
--                   by_cases heq : z = x
--                   -- `[x // a]λx.y` means the original expression is `λx.λx.y`,
--                   -- which is clearly ill-typed because the outer `x` can never be
--                   -- used in `y`!
--                   · simp [heq]
--                     rw [heq] at d_hastype
--                     sorry
--                   · simp [heq] 
--                     apply HasType.lam 
--                     · sorry
--                     · show HasType (AssocList.cons z γ Γ) ([x // a] d) μ
--                       observe d2 : HasType (AssocList.cons z γ (AssocList.cons x α Γ)) d μ
--                       have d2_swapped : HasType (AssocList.cons x α (AssocList.cons z γ Γ)) d μ := sorry
--                       have x_still_fresh : x ∉ AssocList.cons z γ Γ := sorry
--                       exact subst_lemma x_still_fresh (Or.inl d2_swapped) p2
--           | inr pwox => 
--               match pwox with 
--               | @HasType.lam _ _ _ μ _ z_fresh d_hastype => 
--                   simp
--                   by_cases heq : z = x
--                   · simp [heq]
--                     rw [←heq]
--                     exact HasType.lam z_fresh d_hastype
--                   · simp [heq]
--                     apply HasType.lam z_fresh 
--                     have x_still_fresh : x ∉ AssocList.cons z γ Γ := sorry
--                     exact subst_lemma x_still_fresh (Or.inr d_hastype) p2
--     | .app f u => 
--         by
--           cases p1 with
--           | inl pwx =>
--               match pwx with 
--               | @HasType.app _ Γ₁ Γ₂ m n μ ν m_is_fn n_is_ν is_append => 
--                   simp
--                   have x_in_only_one := lem1 x_fresh is_append
--                   match x_in_only_one with 
--                   | .inl ⟨Γ₃, ⟨partof, x_fresh_in_Γ₂⟩⟩ => 
--                       /- let ⟨Γ₃, partof⟩ := @extract_context α Γ₁ x x_in_Γ₁ -/
--                       let m_still_fn : HasType Γ₃ ([x // a] m) (μ.arrow ν) :=
--                         by 
--                           have m_is_fn_with_Γ₃ := equiv_context_replacable m_is_fn (symm partof)
--                           exact subst_lemma x_fresh_in_Γ₃ (Or.inl m_is_fn_with_Γ₃) p2
--                       let n_still_ν : HasType Γ₂ ([x // a] n) μ := 
--                         by  
--                           exact subst_lemma x_fresh_in_Γ₂ (Or.inr n_is_ν) p2
-- 
--                       apply HasType.app 
--                       · exact m_still_fn
--                       · exact n_still_ν
--                       · sorry
--                   | .inr _ => sorry
--                   /- | .inr ⟨Γ₃, ⟨partof, x_fresh_in_Γ₂⟩⟩ => sorry -/
--           | inr pwox => 
--               match pwox with 
--               | @HasType.app _ Γ₁ Γ₂ m n μ ν m_is_fn n_is_ν is_append => 
--                   simp
--                   have x_fresh_in_Γ₁ : x ∉ Γ₁ := sorry
--                   have x_fresh_in_Γ₂ : x ∉ Γ₂ := sorry
--                   show HasType Γ (([x // a] m).app ([x // a] n)) ν
--                   apply HasType.app 
--                   · exact subst_lemma x_fresh_in_Γ₁ (Or.inr m_is_fn) p2
--                   · exact subst_lemma x_fresh_in_Γ₂ (Or.inr n_is_ν) p2
--                   · exact is_append
-- 
-- theorem preservation {τ e₁ e₂}
--   (e₁_is_τ : HasType .nil e₁ τ)
--   (e₁_steps_e₂ : Step e₁ e₂)
--   : HasType .nil e₂ τ := 
--     match e₁_steps_e₂ with 
--     | @Step.app_left f₁ f₂ e f₁_steps_f₂ => 
--         match e₁_is_τ with 
--         | @HasType.app _ Γ₁ Γ₂ _ _ α β f₁_is_fn e_is_ty nil_is_Γ₁_append_Γ₂ => 
--             by
--               have Γ₁_is_nil : Γ₁ = AssocList.nil := sorry
--               have Γ₂_is_nil : Γ₂ = AssocList.nil := sorry
--               rw [Γ₁_is_nil] at f₁_is_fn
--               rw [Γ₁_is_nil] at nil_is_Γ₁_append_Γ₂
--               exact HasType.app (preservation f₁_is_fn f₁_steps_f₂) e_is_ty nil_is_Γ₁_append_Γ₂
--     | @Step.app_right f u₁ u₂ u₁_steps_u₂ =>
--         match e₁_is_τ with 
--         | @HasType.app _ Γ₁ Γ₂ _ _ α β f_is_fn u₁_is_α nil_is_Γ₁_append_Γ₂ => 
--             by
--               have Γ₂_is_nil : Γ₂ = AssocList.nil := sorry
--               rw [Γ₂_is_nil] at u₁_is_α
--               rw [Γ₂_is_nil] at nil_is_Γ₁_append_Γ₂
--               exact HasType.app f_is_fn (preservation u₁_is_α u₁_steps_u₂) nil_is_Γ₁_append_Γ₂
--     | @Step.app_lam x α e a => 
--         match e₁_is_τ with 
--         | @HasType.app _ Γ₁ Γ₂ _ _ _ β f_is_fn a_is_α Γ_is_Γ₁_append_Γ₂ => 
--             match f_is_fn with 
--             | @HasType.lam _ _ _ _ _ x_fresh_in_Γ₁ bty => 
--                 by
--                   -- have is_same : context_append Γ₁ AssocList.nil ++ Γ₂ = Γ :=
--                   --   by
--                   --     simp [context_append]
--                   --     exact Eq.symm Γ_is_Γ₁_append_Γ₂
--                   -- rw [←is_same]
--                   have Γ₁_is_nil : Γ₁ = AssocList.nil := sorry
--                   have Γ₂_is_nil : Γ₂ = AssocList.nil := sorry
--                   rw [←Γ₁_is_nil]
--                   exact subst_lemma x_fresh_in_Γ₁ (Or.inl bty) (Γ₂_is_nil ▸ a_is_α)
-- 
-- 
-- 
-- -- theorem preservation {Γ τ e₁ e₂}
-- --   (e₁_is_τ : HasType Γ e₁ τ)
-- --   (e₁_steps_e₂ : Step e₁ e₂)
-- --   : HasType Γ e₂ τ := 
-- --     match e₁_steps_e₂ with 
-- --     | Step.app_left f₁_steps_f₂ => 
-- --         match e₁_is_τ with 
-- --         | HasType.app f₁_is_fn e_is_ty is_append => 
-- --             HasType.app (preservation f₁_is_fn f₁_steps_f₂) e_is_ty is_append
-- --     | Step.app_right u₁_steps_u₂ =>
-- --         match e₁_is_τ with 
-- --         | HasType.app f_is_fn u₁_is_ty is_append => 
-- --             HasType.app f_is_fn (preservation u₁_is_ty u₁_steps_u₂) is_append
-- --     | @Step.app_lam x α e a => 
-- --         match e₁_is_τ with 
-- --         | @HasType.app Γ Γ₁ Γ₂ _ _ _ β f_is_fn a_is_α is_append => 
-- --             match f_is_fn with 
-- --             | @HasType.lam _ _ _ _ _ bty _ => 
-- --                 by
-- --                   have is_same : context_append Γ₁ AssocList.nil ++ Γ₂ = Γ :=
-- --                     by
-- --                       simp [context_append]
-- --                       exact Eq.symm is_append
-- --                   rw [←is_same]
-- --                   _
-- 
-- -- lemma subst_lemma {x e a α β} 
-- --   (e_is_β_with_α : HasType (.cons x α .nil) e β )
-- --   (v_is_α : HasType .nil a α)
-- --   : HasType .nil ([x // a]e) β := 
-- --     match e with 
-- --     | .var y => 
-- --         by 
-- --           by_cases heq : y = x 
-- --           . simp [heq]
-- --             rw [heq] at e_is_β_with_α
-- --             cases e_is_β_with_α with 
-- --             | var => exact v_is_α
-- --           . simp [heq]
-- --             cases e_is_β_with_α with
-- --             | var => contradiction
-- --     | .lam z γ d => 
-- --         by
-- --           match e_is_β_with_α with 
-- --           | @HasType.lam _ _ _ μ _ z_fresh d_is_μ =>
-- --               simp 
-- --               by_cases heq : z = x 
-- --               -- `[x // a]λx.y` means the original expression is `λx.λx.y`,
-- --               -- which is clearly ill-typed because the outer `x` can never be
-- --               -- used in `y`!
-- --               · simp [heq]
-- --                 rw [heq] at d_is_μ 
-- --                 have z_not_fresh : z ∈ AssocList.cons x α AssocList.nil :=
-- --                   by 
-- --                     rw [heq]
-- --                     simp [Membership.mem, AssocList.contains]
-- --                 contradiction
-- --               · simp [heq]
-- --                 apply HasType.lam 
-- --                 · simp [Membership.mem, AssocList.contains]
-- --                 · rw [nil_append_is_same]
-- --                   _
-- --     | _ => sorry

