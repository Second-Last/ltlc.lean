# Linearly Typed Lambda Calculus formalized in Lean 4

STLC (Simply Typed Lambda Calculus) need no further explanations. This repo
explores a _linear_ variant of STLC, which I will name LTLC (Linearly Typed
Lambda Calculus). In this calculus, every variable must be consumed exactly
once. For example, `λx.λy.y` is invalid because `x` is used 0 times in its body;
`λx.x x` is also invalid because `x` is used 2 times in its body; `λx.x` is
valid because `x` is used exactly 1 time in its body.

To my knowledge, it's first proposed in 1990 by Phil Wadler in his paper _Linear
types can change the world!_. Wadler's version of the LTLC includes
sum types and product types, essentially bringing ADTs to lambda calculus.
This turns out to be too hard to prove in Lean, therefore we formalize the
simplest LTLC we can have: the STLC that we all know and love
plus an additional restriction that every variable must be used exactly once.

The syntax remains the same. The small/big step semantics remain the same. The
only change is in the typing semantics.

Then, because Wadler didn't in his paper, we prove Progress and Preservation on
LTLC. At the time of this writing, Progress has been finished but Preservation
has not, mostly due to difficulties in dealing with the "merging" of two
contexts when proving the substitution lemma.

```lean4
inductive HasType : Context → LtlcTerm → LtlcType → Prop
  | var {x τ} : ...
  | lam {Γ x α β body} : ...
  | app 
    {Γ₁ Γ₂ t u α β}
    (t_is_fn : HasType Γ₁ t (.arrow α β))
    (u_is_α : HasType Γ₂ u α)
    (is_append : Γ ≈ Γ₁ ++ Γ₂) -- this parameter is the source of all pain
    : HasType Γ (.app t u) β
```

The source is well-structured with filenames that should indicate clearly what
its corresponding file contains.
