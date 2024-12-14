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

notation "Context" => AssocList String LtlcType

instance : Membership String Context where
  mem l x := l.contains x = true

def context_append (x y : Context) : Context :=
    match y with 
    | .nil => x 
    | .cons k v ys => .cons k v (context_append x ys)

instance : Append Context where
  append x y := context_append x y

-- inductive Context 
--   | empty : Context 
--   | single : String → LtlcType → Context 
--   | combine : Context → Context → Context
-- 
-- def Context.contains (c : Context) (x : String) : Bool :=
--   match c with 
--   | .empty => false 
--   | .single y _ => x = y 
--   | .combine l r => l.contains x || r.contains x
-- 
-- instance : Membership String Context where 
--   mem l x := l.contains x = true

inductive HasType : Context → LtlcTerm → LtlcType → Prop
  | var {x τ} : HasType (.cons x τ .nil) (.var x) τ
  | lam 
    {Γ x α β body}
    (x_fresh : x ∉ Γ)
    (v_hastype : HasType (.cons x α Γ) body β)
    : HasType Γ (LtlcTerm.lam x α body) (.arrow α β)
  | app 
    {Γ₁ Γ₂ t u α β}
    (t_is_fn : HasType Γ₁ t (.arrow α β))
    (u_is_α : HasType Γ₂ u α)
    (is_append : Γ = Γ₁ ++ Γ₂)
    : HasType Γ (.app t u) β

@[simp]
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

lemma cons_is_append_single {Γ : Context} {x : String} {α : LtlcType}
  : AssocList.cons x α Γ = Γ ++ (AssocList.cons x α AssocList.nil) := rfl

lemma nil_append_is_same {Γ : Context} : AssocList.nil ++ Γ = Γ := sorry

theorem subst_preserves_type {Γ x α β e a} 
  /- (x_not_in_Γ₂ : x ∉ Γ₂) -/
  (p1 : HasType (.cons x α Γ) e β)
  (p2 : HasType .nil a α)
  : HasType Γ ([x // a] e) β :=
    match e with 
    | .var y => 
        by 
          by_cases heq : y = x 
          . simp [heq]
            rw [heq] at p1 
            cases p1 with 
            | var => 
                exact p2
          . simp [heq]
            cases p1 with
            | var => contradiction
    | .lam z γ d =>
        by 
          match p1 with 
          | @HasType.lam _ _ _ μ _ z_fresh d_hastype => 
              simp
              by_cases heq : z = x
              -- `[x // a]λx.y` means the original expression is `λx.λx.y`,
              -- which is clearly ill-typed because the outer `x` can never be
              -- used in `y`!
              · simp [heq]
                rw [heq] at d_hastype
                sorry
              · simp [heq] 
                apply HasType.lam 
                · sorry
                · show HasType (AssocList.cons z γ Γ) ([x // a] d) μ
                  observe d2 : HasType (AssocList.cons z γ (AssocList.cons x α Γ)) d μ
                  have d2_swapped : HasType (AssocList.cons x α (AssocList.cons z γ Γ)) d μ := sorry
                  exact subst_preserves_type d2_swapped p2
    | .app f u => 
        by
          match p1 with 
          | @HasType.app _ Γ₁ Γ₂ m n μ ν m_is_fn n_is_ν is_append => 
              simp
              _

-- theorem preservation {Γ τ e₁ e₂}
--   (e₁_is_τ : HasType Γ e₁ τ)
--   (e₁_steps_e₂ : Step e₁ e₂)
--   : HasType Γ e₂ τ := 
--     match e₁_steps_e₂ with 
--     | Step.app_left f₁_steps_f₂ => 
--         match e₁_is_τ with 
--         | HasType.app f₁_is_fn e_is_ty is_append => 
--             HasType.app (preservation f₁_is_fn f₁_steps_f₂) e_is_ty is_append
--     | Step.app_right u₁_steps_u₂ =>
--         match e₁_is_τ with 
--         | HasType.app f_is_fn u₁_is_ty is_append => 
--             HasType.app f_is_fn (preservation u₁_is_ty u₁_steps_u₂) is_append
--     | @Step.app_lam x α e a => 
--         match e₁_is_τ with 
--         | @HasType.app Γ Γ₁ Γ₂ _ _ _ β f_is_fn a_is_α is_append => 
--             match f_is_fn with 
--             | @HasType.lam _ _ _ _ _ bty _ => 
--                 by
--                   have is_same : context_append Γ₁ AssocList.nil ++ Γ₂ = Γ :=
--                     by
--                       simp [context_append]
--                       exact Eq.symm is_append
--                   rw [←is_same]
--                   _

-- lemma subst_lemma {x e a α β} 
--   (e_is_β_with_α : HasType (.cons x α .nil) e β )
--   (v_is_α : HasType .nil a α)
--   : HasType .nil ([x // a]e) β := 
--     match e with 
--     | .var y => 
--         by 
--           by_cases heq : y = x 
--           . simp [heq]
--             rw [heq] at e_is_β_with_α
--             cases e_is_β_with_α with 
--             | var => exact v_is_α
--           . simp [heq]
--             cases e_is_β_with_α with
--             | var => contradiction
--     | .lam z γ d => 
--         by
--           match e_is_β_with_α with 
--           | @HasType.lam _ _ _ μ _ z_fresh d_is_μ =>
--               simp 
--               by_cases heq : z = x 
--               -- `[x // a]λx.y` means the original expression is `λx.λx.y`,
--               -- which is clearly ill-typed because the outer `x` can never be
--               -- used in `y`!
--               · simp [heq]
--                 rw [heq] at d_is_μ 
--                 have z_not_fresh : z ∈ AssocList.cons x α AssocList.nil :=
--                   by 
--                     rw [heq]
--                     simp [Membership.mem, AssocList.contains]
--                 contradiction
--               · simp [heq]
--                 apply HasType.lam 
--                 · simp [Membership.mem, AssocList.contains]
--                 · rw [nil_append_is_same]
--                   _
--     | _ => sorry

theorem preservation {τ e₁ e₂}
  (e₁_is_τ : HasType .nil e₁ τ)
  (e₁_steps_e₂ : Step e₁ e₂)
  : HasType .nil e₂ τ := 
    match e₁_steps_e₂ with 
    | @Step.app_left f₁ f₂ e f₁_steps_f₂ => 
        match e₁_is_τ with 
        | @HasType.app _ Γ₁ Γ₂ _ _ α β f₁_is_fn e_is_ty nil_is_Γ₁_append_Γ₂ => 
            by
              have Γ₁_is_nil : Γ₁ = AssocList.nil := sorry
              have Γ₂_is_nil : Γ₂ = AssocList.nil := sorry
              rw [Γ₁_is_nil] at f₁_is_fn
              rw [Γ₁_is_nil] at nil_is_Γ₁_append_Γ₂
              exact HasType.app (preservation f₁_is_fn f₁_steps_f₂) e_is_ty nil_is_Γ₁_append_Γ₂
    | @Step.app_right f u₁ u₂ u₁_steps_u₂ =>
        match e₁_is_τ with 
        | @HasType.app _ Γ₁ Γ₂ _ _ α β f_is_fn u₁_is_α nil_is_Γ₁_append_Γ₂ => 
            by
              have Γ₂_is_nil : Γ₂ = AssocList.nil := sorry
              rw [Γ₂_is_nil] at u₁_is_α
              rw [Γ₂_is_nil] at nil_is_Γ₁_append_Γ₂
              exact HasType.app f_is_fn (preservation u₁_is_α u₁_steps_u₂) nil_is_Γ₁_append_Γ₂
    | @Step.app_lam x α e a => 
        match e₁_is_τ with 
        | @HasType.app _ Γ₁ Γ₂ _ _ _ β f_is_fn a_is_α Γ_is_Γ₁_append_Γ₂ => 
            match f_is_fn with 
            | @HasType.lam _ _ _ _ _ _ bty => 
                by
                  -- have is_same : context_append Γ₁ AssocList.nil ++ Γ₂ = Γ :=
                  --   by
                  --     simp [context_append]
                  --     exact Eq.symm Γ_is_Γ₁_append_Γ₂
                  -- rw [←is_same]
                  have Γ₁_is_nil : Γ₁ = AssocList.nil := sorry
                  have Γ₂_is_nil : Γ₂ = AssocList.nil := sorry
                  rw [←Γ₁_is_nil]
                  apply subst_preserves_type bty
                  rw [←Γ₂_is_nil]
                  exact a_is_α
