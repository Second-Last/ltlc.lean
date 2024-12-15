import Mathlib

import Ltlc.Terms
import Ltlc.Types

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

