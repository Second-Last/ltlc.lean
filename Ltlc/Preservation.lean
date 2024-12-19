import Mathlib

import Ltlc.Terms
import Ltlc.Types 
import Ltlc.Context

import Ltlc.Step
import Ltlc.Typing

import Ltlc.Utils

-- For AssocList
open Lean

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

lemma equiv_context_replacable {Γ₁ Γ₂ : Context}
  (e_is_τ : HasType Γ₁ e τ)
  (Γ₁_equiv_Γ₂ : Γ₁ ≈ Γ₂)
  : HasType Γ₂ e τ := 
    by
      match e_is_τ with 
      | @HasType.var x _ => 
          rw [equiv_singleton_eq Γ₁_equiv_Γ₂]
          exact HasType.var
      | @HasType.app _ G H t u α β t_is_fn u_is_α is_append => 
          let Γ₂_is_append : Γ₂ ≈ G ++ H := 
            Trans.trans (symm Γ₁_equiv_Γ₂) is_append
          exact HasType.app t_is_fn u_is_α Γ₂_is_append
/-
  | lam 
    {Γ x α β body}
    (x_fresh : ¬Bound x Γ)
    (v_hastype : HasType (.cons x α Γ) body β)
    : HasType Γ (LtlcTerm.lam x α body) (.arrow α β)
-/
      | @HasType.lam _ x α β body x_fresh v_hastype => 
          apply HasType.lam
          · by_contra hx
            let x_not_fresh : Bound x Γ₁ := 
              bound_equiv_replacable hx (symm Γ₁_equiv_Γ₂)
            contradiction
          · apply equiv_context_replacable v_hastype
            let ⟨leneq, ⟨eq12, eq21⟩⟩ := Γ₁_equiv_Γ₂
            apply And.intro
            · simp [AssocList.length]
              exact leneq
            · apply And.intro
              · intro s σ sσ_in_ctx
                by_cases x_is_s : x = s
                · simp [x_is_s]
                  by_cases σ_is_α : σ = α
                  · simp [σ_is_α]
                    exact InContext.aha s α Γ₂
                  · cases sσ_in_ctx with 
                    | aha => contradiction
                    | hang_on => 
                        exact InContext.hang_on s σ s α Γ₂ (eq12 s σ (by assumption))
                · cases sσ_in_ctx with 
                  | aha => contradiction
                  | hang_on => 
                      exact InContext.hang_on s σ x α Γ₂ (eq12 s σ (by assumption))
              · intro s σ sσ_in_ctx
                by_cases x_is_s : x = s
                · simp [x_is_s]
                  by_cases σ_is_α : σ = α
                  · simp [σ_is_α]
                    exact InContext.aha s α Γ₁
                  · cases sσ_in_ctx with 
                    | aha => contradiction
                    | hang_on => 
                        exact InContext.hang_on s σ s α Γ₁ (eq21 s σ (by assumption))
                · cases sσ_in_ctx with 
                  | aha => contradiction
                  | hang_on => 
                      exact InContext.hang_on s σ x α Γ₁ (eq21 s σ (by assumption))
            

-- lemma cons_is_append_single {Γ : Context} {x : String} {α : LtlcType}
--   : AssocList.cons x α Γ = Γ ++ (AssocList.cons x α AssocList.nil) := rfl

-- theorem swapping_perserves
--   (e_is_τ : HasType (.cons x α (.cons y β Γ)) e τ)
--   (x_not_y : x ≠ y)
--   : HasType (.cons y β (.cons x α Γ)) e τ := 
--     by 
--       match e_is_τ with
--       | @HasType.lam _ m μ ν b m_fresh b_is_ν => 
--           apply HasType.lam
--           · sorry 
--           · _
--       | .app _ _ _ => sorry

theorem subst_lemma {Γ x α β e a} 
  (x_fresh : ¬Bound x Γ)
  (p1 : (HasType (.cons x α Γ) e β) ∨ HasType Γ e β)
  (p2 : HasType .nil a α)
  : HasType Γ ([x // a] e) β :=
     match e with 
     | .var y => 
         by 
           by_cases heq : y = x 
           . simp [heq]
             rw [heq] at p1 
             cases p1 with 
             | inl pwx => 
                 cases pwx with
                 | var => exact p2
             | inr pwox =>
                 cases pwox with 
                 | var => 
                     have x_not_fresh : Bound x (AssocList.cons x β AssocList.nil) := 
                       by
                         exact Bound.yochat x β AssocList.nil
                     contradiction
           . simp [heq]
             cases p1 with
             | inl pwx => 
                 cases pwx with
                 | var => contradiction
             | inr pwox =>
                 cases pwox with 
                 | var => exact HasType.var
     | .lam z γ d =>
         by 
           cases p1 with
           | inl pwx => 
               match pwx with 
               | @HasType.lam _ _ _ μ _ z_fresh d_hastype => 
                   simp
                   by_cases heq : z = x
                   -- `[x // a]λx.y` means the original expression is `λx.λx.y`,
                   -- which is clearly ill-typed because the outer `x` can never be
                   -- used in `y`!
                   · simp [heq]
                     rw [heq] at d_hastype
                     rw [←heq] at z_fresh
                     have z_not_fresh : Bound z (AssocList.cons z α Γ) := Bound.yochat z α Γ
                     contradiction
                   · simp [heq] 
                     apply HasType.lam 
                     · intro z_not_fresh_in_Γ
                       let z_not_fresh : Bound z (AssocList.cons x α Γ)
                         := Bound.brb z x α Γ heq z_not_fresh_in_Γ
                       contradiction
                     · show HasType (AssocList.cons z γ Γ) ([x // a] d) μ
                       observe d2 : HasType (AssocList.cons z γ (AssocList.cons x α Γ)) d μ
                       have d2_swapped : HasType (AssocList.cons x α (AssocList.cons z γ Γ)) d μ 
                        := equiv_context_replacable d2 swap_12_equiv
                       have x_still_fresh : ¬Bound x (AssocList.cons z γ Γ) := 
                          by
                            intro x_not_fresh_with_z
                            cases x_not_fresh_with_z with 
                            | yochat => contradiction
                            | brb => contradiction
                       exact subst_lemma x_still_fresh (Or.inl d2_swapped) p2
           | inr pwox => 
               match pwox with 
               | @HasType.lam _ _ _ μ _ z_fresh d_hastype => 
                   simp
                   by_cases heq : z = x
                   · simp [heq]
                     rw [←heq]
                     exact HasType.lam z_fresh d_hastype
                   · simp [heq]
                     apply HasType.lam z_fresh 
                     have x_still_fresh : ¬Bound x (AssocList.cons z γ Γ) := 
                      by 
                        intro x_not_fresh_with_z
                        cases x_not_fresh_with_z with
                        | yochat => contradiction
                        | brb => contradiction
                     exact subst_lemma x_still_fresh (Or.inr d_hastype) p2
      | _ => sorry
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

theorem preservation {τ e₁ e₂}
  (e₁_is_τ : HasType .nil e₁ τ)
  (e₁_steps_e₂ : Step e₁ e₂)
  : HasType .nil e₂ τ := 
    match e₁_steps_e₂ with 
    | @Step.app_left f₁ f₂ e f₁_steps_f₂ => 
        match e₁_is_τ with 
        | @HasType.app _ Γ₁ Γ₂ _ _ α β f₁_is_fn e_is_ty nil_is_Γ₁_append_Γ₂ => 
            by
              let ⟨Γ₁_is_nil, Γ₂_is_nil⟩ := nil_append_nil_nil nil_is_Γ₁_append_Γ₂
              rw [Γ₁_is_nil] at f₁_is_fn
              rw [Γ₁_is_nil] at nil_is_Γ₁_append_Γ₂
              exact HasType.app (preservation f₁_is_fn f₁_steps_f₂) e_is_ty nil_is_Γ₁_append_Γ₂
    | @Step.app_right f u₁ u₂ u₁_steps_u₂ =>
        match e₁_is_τ with 
        | @HasType.app _ Γ₁ Γ₂ _ _ α β f_is_fn u₁_is_α nil_is_Γ₁_append_Γ₂ => 
            by
              let ⟨_, Γ₂_is_nil⟩ := nil_append_nil_nil nil_is_Γ₁_append_Γ₂
              rw [Γ₂_is_nil] at u₁_is_α
              rw [Γ₂_is_nil] at nil_is_Γ₁_append_Γ₂
              exact HasType.app f_is_fn (preservation u₁_is_α u₁_steps_u₂) nil_is_Γ₁_append_Γ₂
    | @Step.app_lam x α e a => 
        match e₁_is_τ with 
        | @HasType.app _ Γ₁ Γ₂ _ _ _ β f_is_fn a_is_α nil_is_Γ₁_append_Γ₂ => 
            match f_is_fn with 
            | @HasType.lam _ _ _ _ _ x_fresh_in_Γ₁ bty => 
                by
                  let ⟨Γ₁_is_nil, Γ₂_is_nil⟩ := nil_append_nil_nil nil_is_Γ₁_append_Γ₂
                  rw [←Γ₁_is_nil]
                  exact subst_lemma x_fresh_in_Γ₁ (Or.inl bty) (Γ₂_is_nil ▸ a_is_α)
