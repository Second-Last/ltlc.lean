import Mathlib
import Ltlc.Terms
import Ltlc.Types

-- For AssocList
open Lean

def Lean.AssocList.length : AssocList α β → ℕ 
  | AssocList.cons _ _ xs => 1 + AssocList.length xs
  | AssocList.nil => 0

notation "Context" => AssocList String LtlcType

inductive Bound : String → Context → Prop
  | yochat x α c : Bound x (.cons x α c)
  | brb x y β cs : ¬(x = y) → Bound x cs → Bound x (.cons y β cs)

inductive InContext : String → LtlcType → Context → Prop 
  | aha x α c : InContext x α (.cons x α c)
  | hang_on x α y β cs : InContext x α cs → InContext x α (.cons y β cs)

theorem incontext_is_bound 
  (inctx : InContext x α Γ)
  : Bound x Γ :=
    match inctx with 
    | .aha _ _ Γ' => Bound.yochat x α Γ'
    | .hang_on _ _ y β Γ' inΓ' => 
        by
          by_cases hxy : x = y
          · rw [hxy]
            exact Bound.yochat y β Γ'
          · apply Bound.brb x y β Γ' hxy
            exact incontext_is_bound inΓ'

theorem notbound_is_notincontext
  (notbnd : ¬Bound x Γ)
  : ¬InContext x α Γ :=
    by
      intro inctx
      have bnd := incontext_is_bound inctx
      contradiction

def context_equivalent (a b : Context) : Prop := 
  a.length = b.length 
  ∧ (∀x, ∀α, InContext x α a → InContext x α b)
  ∧ (∀y, ∀β, InContext y β b → InContext y β a)

-- cons basically becomes `insert` for the sake of easier to use.
@[simp]
def context_append (x y : Context) : Context :=
    match y with 
    | .nil => x 
    | .cons k v ys => .cons k v (context_append x ys)

instance : Setoid Context where 
  r := context_equivalent
  iseqv := {
    refl := by simp [context_equivalent]

    symm := 
      by
        intro Γ₁ Γ₂
        simp [context_equivalent]
        intro eql lefteq righteq
        apply And.intro
        . exact Eq.symm eql
        · apply And.intro
          · assumption
          · assumption

    trans := 
      by 
        intro Γ₁ Γ₂ Γ₃
        simp [context_equivalent]
        intro eql12 leq12 req12 eql23 leq23 req23
        apply And.intro
        · exact Eq.trans eql12 eql23
        · apply And.intro
          · exact fun x α a => leq23 x α (leq12 x α (req12 x α (leq12 x α a)))
          · exact fun y β a => req12 y β (leq12 y β (req12 y β (req23 y β a)))
  }

theorem swap_12_equiv {Γ : Context} :
  AssocList.cons x α (.cons y β Γ) ≈ .cons y β (.cons x α Γ) := by
    apply And.intro
    · aesop
    · apply And.intro
      · intro z γ z_in_ctx
        match z_in_ctx with 
        | .aha _ _ _ => 
            apply InContext.hang_on z γ y β
            exact InContext.aha z γ Γ
        | .hang_on _ _ _ _ _ still_in_ctx => 
            match still_in_ctx with 
            | .aha _ _ _ => 
                exact InContext.aha z γ (AssocList.cons x α Γ)
            | .hang_on _ _ _ _ _ fin_in_ctx =>
                apply InContext.hang_on z γ y β
                apply InContext.hang_on z γ x α
                exact fin_in_ctx
      · intro z γ z_in_ctx
        match z_in_ctx with 
        | .aha _ _ _ => 
            apply InContext.hang_on z γ x α
            exact InContext.aha z γ Γ
        | .hang_on _ _ _ _ _ still_in_ctx => 
            match still_in_ctx with 
            | .aha _ _ _ => 
                exact InContext.aha z γ (AssocList.cons y β Γ)
            | .hang_on _ _ _ _ _ fin_in_ctx =>
                apply InContext.hang_on z γ x α
                apply InContext.hang_on z γ y β
                exact fin_in_ctx

theorem bound_to_inctx (bnd : Bound x Γ) : ∃α, InContext x α Γ := 
  by
    match bnd with 
    | .yochat _ τ Γ' => 
        exact ⟨τ, InContext.aha x τ Γ'⟩
    | .brb _ y β Γ' xnoty stillbnd => 
        let ⟨τ, x_in_ctx⟩ := bound_to_inctx stillbnd
        exact ⟨τ, InContext.hang_on x τ y β Γ' x_in_ctx⟩

theorem bound_equiv_replacable {Γ₁ Γ₂ : Context}
  (bnd : Bound x Γ₁)
  (is_equiv : Γ₁ ≈ Γ₂)
  : Bound x Γ₂ :=
    by
      let ⟨eqlen, ⟨eq12, eq21⟩⟩ := is_equiv
      let ⟨α, x_inctx_Γ₁⟩ := bound_to_inctx bnd
      let x_inctx_Γ₂ : InContext x α Γ₂ := eq12 x α x_inctx_Γ₁
      exact incontext_is_bound x_inctx_Γ₂

@[simp]
instance : Append Context where
  append x y := context_append x y

lemma mem_append_mem {x : String} {Γ₁ Γ₂ : Context} 
  (x_mem : InContext x α Γ₁) : InContext x α (Γ₁ ++ Γ₂) := 
    match Γ₂ with 
    | .nil => by trivial
    | .cons y β ys => 
        by
          show InContext x α (AssocList.cons y β (Γ₁ ++ ys))
          by_cases hxy : x = y
          · rw [←hxy]
            by_cases hατ : α = β
            · rw [←hατ]
              exact InContext.aha x α (Γ₁ ++ ys)
            · apply InContext.hang_on x α x β (Γ₁ ++ ys)
              exact mem_append_mem x_mem
          · apply InContext.hang_on x α y β
            exact mem_append_mem x_mem

lemma nil_append_nil_nil {Γ₁ Γ₂ : Context} :
  AssocList.nil ≈ Γ₁ ++ Γ₂ 
  → Γ₁ = AssocList.nil ∧ Γ₂ = AssocList.nil
  := by
    intro equiv_append
    apply And.intro 
    · by_contra notnil
      match Γ₁ with
      | AssocList.nil => contradiction 
      | AssocList.cons x α xs => 
          simp [.≈., Setoid.r, context_equivalent] at equiv_append
          let ⟨_, ⟨_, rhx⟩⟩ := equiv_append
          let x_in_nil := rhx x α (mem_append_mem (InContext.aha x α xs))
          contradiction
    · by_contra notnil 
      match Γ₂ with 
      | AssocList.nil => contradiction 
      | AssocList.cons y β ys => 
          simp [.≈., Setoid.r, context_equivalent] at equiv_append
          let ⟨_, ⟨lhx, rhx⟩⟩ := equiv_append
          let y_in_nili := rhx y β (InContext.aha y β _)
          contradiction

lemma equiv_singleton_eq {x : String} {α : LtlcType}
  (equiv_singleton : AssocList.cons x α AssocList.nil ≈ Γ)
  : Γ = AssocList.cons x α AssocList.nil
  :=
  by
    match Γ with
    | .nil => 
        let ⟨leneq, _⟩ := equiv_singleton
        simp [AssocList.length] at leneq
    | .cons y β .nil =>
        let x_is_y : x = y := by
          by_contra x_not_y
          let ⟨_, ⟨leq, req⟩⟩ := equiv_singleton
          cases leq x α (InContext.aha x α AssocList.nil) with 
          | _ => contradiction
        let α_is_β : α = β := by 
          by_contra α_not_β 
          let ⟨_, ⟨leq, req⟩⟩ := equiv_singleton
          cases leq x α (InContext.aha x α AssocList.nil) with 
          | _ => contradiction
        rw [x_is_y, α_is_β]
    | .cons y β (.cons z γ rest) => 
        let ⟨leneq, _⟩ := equiv_singleton
        simp [AssocList.length] at leneq
