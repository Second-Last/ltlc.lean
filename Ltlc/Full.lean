import Mathlib
import Ltlc.Utils

open Lean
open Mathlib
/- open Batteries -/

inductive LtlcType
  | fn : LtlcType → LtlcType → LtlcType
  | base : List (String × List LtlcType) → LtlcType
  deriving Repr, BEq

inductive LtlcTerm 
  | var : String → LtlcTerm
  | lam : String → LtlcType → LtlcTerm → LtlcTerm
  | app : LtlcTerm → LtlcTerm → LtlcTerm
  | ctor : String → List LtlcTerm → LtlcTerm
  | bcase : LtlcTerm → List (String × List String × LtlcTerm) → LtlcTerm
  deriving Repr, BEq

/- structure ADT where -/
/-   ctors : List (String × List LtlcType) -/

/- def Context := Set (LtlcTerm × LtlcType) -/

def Context := AssocList String LtlcType

instance : Membership String Context where
  mem l x := l.contains x = true

instance : Append Context where
  append x y := AssocList.foldl (λ l x t => l.insert x t) y x

instance : BEq Context where
  beq x y := sorry

inductive HasType : Context → LtlcTerm → LtlcType → Prop
  | var (x : String) (t : LtlcType) : HasType (AssocList.empty.insert x t) (.var x) t
  | lam 
    (a : Context)
    (x : String)
    (u v : LtlcType)
    (body : LtlcTerm)
    (x_fresh : x ∉ a)
    (v_hastype : HasType (a.insert x t) body v)
    : HasType a (LtlcTerm.lam x u body) (LtlcType.fn u v)
  | app 
    (a b : Context)
    (t u : LtlcTerm)
    (m n : LtlcType)
    (t_is_fn : HasType a t (.fn m n))
    (u_is_n : HasType b u m)
    : HasType (a ++ b) (.app t u) n
  | ctor
    {n : ℕ}
    /- {k : ADT} -/
    (c : String)
    (ctors : List (String × List LtlcType))
    (ctxs : Vector Context n)
    (terms : Vector LtlcTerm n)
    (tys : Vector LtlcType n)
    (all_welltyped : Vector.all (λ (arg : Context × LtlcTerm × LtlcType) => match arg with | ⟨a, u, t⟩ => HasType a u t) (Vector.zip3 ctxs terms tys))
    -- (all_welltyped : ∀ x ∈ Vector.zip3 ctxs terms tys, (λ (arg : Context × LtlcTerm × LtlcType) => match arg with | ⟨a, u, t⟩ => HasType a u v) x)
    : HasType (List.foldl append AssocList.empty ctxs.toList) (.ctor c terms.toList) (.base ctors)
