import Mathlib
import Ltlc.Terms
import Ltlc.Types

-- For AssocList
open Lean

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

def context_equivalent (a b : Context) : Prop := 
  (∀x, ∀α, InContext x α a → InContext x α b)
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
        intro lefteq righteq
        apply And.intro
        · assumption
        · assumption

    trans := 
      by 
        intro Γ₁ Γ₂ Γ₃
        simp [context_equivalent]
        intro leq12 req12
        intro leq23 req23
        apply And.intro
        · exact fun x α a => leq23 x α (leq12 x α (req12 x α (leq12 x α a)))
        · exact fun y β a => req12 y β (leq12 y β (req12 y β (req23 y β a)))
  }

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
          let ⟨_, rhx⟩ := equiv_append
          let x_in_nil := rhx x α (mem_append_mem (InContext.aha x α xs))
          contradiction
    · by_contra notnil 
      match Γ₂ with 
      | AssocList.nil => contradiction 
      | AssocList.cons y β ys => 
          simp [.≈., Setoid.r, context_equivalent] at equiv_append
          let ⟨lhx, rhx⟩ := equiv_append
          let y_in_nili := rhx y β (InContext.aha y β _)
          contradiction
