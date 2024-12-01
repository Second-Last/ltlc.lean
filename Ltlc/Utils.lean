import Mathlib

open Lean
open Mathlib

def uncurry3 {α β γ ρ : Type} (f : α → β → γ → ρ) : α × β × γ → ρ := 
  λ arg =>
    match arg with 
    | ⟨a, b, c⟩ => f a b c

def List.All (p : α → Prop) (lst : List α) : Prop :=
  match lst with
  | [] => True
  | x :: xs => p x ∧ List.All p xs

def Vector.zip3 {α : Type u} {β : Type v} {γ : Type w} {n : ℕ} (v1 : Vector α n) (v2 : Vector β n) (v3 : Vector γ n)
  : Vector (α × β × γ) n := Vector.zipWith Prod.mk v1 (Vector.zipWith Prod.mk v2 v3)

def Vector.all {n : ℕ} (f : α → Prop) (lst : Vector α n) : Prop :=
  match lst with
  | ⟨lst, _⟩ => List.All f lst
