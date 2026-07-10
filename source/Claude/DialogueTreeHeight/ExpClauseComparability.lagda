PROTOTYPE (not in the tour, not depended on): the arithmetic mechanism by which
the `ω^(–)` functor dissolves the "single clause cannot bound both linear and
squaring" wall.

Design note: `dialogue-tree-height-decoupling.md`. A single hereditary transformer
clause must upper-bound BOTH the linear outputs of `K`/`S`/application (in the
multiplier world, `M₁ ⊗ ω`) AND the squaring output of self-composition
(`M₁ ⊗ M₁`). In the MULTIPLIER world these are incomparable: `M₁ ⊗ ω ≤ M₁ ⊗ M₁`
holds only under the extra hypothesis `ω ≤ M₁` (below, `mult-coeff-needs-hyp`) —
false for small `M₁`, so no fixed clause dominates uniformly. This is exactly the
wall ("no closed class containing squaring is known").

Writing the multiplier as `ω^ β` moves the degree into the EXPONENT, where a
higher coefficient dominates a lower one UNCONDITIONALLY: `β ≤ β ⊗ ι[2]` holds for
every `β` (`x-≤-x⊗`, no hypothesis), so a coefficient-`2` exponent clause bounds
the coefficient-`1` (linear/base) output uniformly (below, `exp-coeff-dominates`).
The contrast between the two lemmas — one needs a hypothesis, the other does not —
is the whole content of why the functor helps.

This is a fragment of the mechanism, not a closure proof. The hereditary predicate
and its fundamental theorem (in particular the higher-order recursor majorant,
still the open residual) are the development this underpins; the conjecture
remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.ExpClauseComparability
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import Claude.BrouwerOrdinals.Order fe using (_≤_ ; _⊕_ ; ≤-Z ; ≤-S)
open import Claude.BrouwerOrdinals.Orbit fe using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (ω^_ ; ω^-mono ; ⊗-mono-left ; ⊗-mono-right)
open import Claude.BrouwerOrdinals.AffineClosure fe using (x-≤-x⊗)

\end{code}

In the EXPONENT world: a coefficient-`2` clause dominates the coefficient-`1`
(linear/base) output, for EVERY exponent `β₁` and offset `e` — no hypothesis.
`β₁ ≤ β₁ ⊗ ι[2]` is unconditional, so `ω^ (β₁ ⊕ e) ≤ ω^ (β₁ ⊗ ι[2] ⊕ e)`.

\begin{code}

exp-coeff-dominates : (β₁ e : 𝓑)
                    → ω^ (β₁ ⊕ e) ≤ ω^ ((β₁ ⊗ ι[ 2 ]) ⊕ e)
exp-coeff-dominates β₁ e =
 ω^-mono (⊕-mono-left (x-≤-x⊗ β₁ ι[ 2 ] (≤-S ≤-Z)) e)

\end{code}

In the MULTIPLIER world: the same domination — linear `M₁ ⊗ ω` below squaring
`M₁ ⊗ M₁` — is available ONLY under the hypothesis `ω ≤ M₁`. Without it there is
no uniform bound (take `M₁` finite: `M₁ ⊗ ω = ω` but `M₁ ⊗ M₁` is finite). This is
the wall the functor removes.

\begin{code}

mult-coeff-needs-hyp : (M₁ M : 𝓑) → ω ≤ M₁
                     → ((M₁ ⊗ ω) ⊗ M) ≤ ((M₁ ⊗ M₁) ⊗ M)
mult-coeff-needs-hyp M₁ M ω≤M₁ =
 ⊗-mono-left (⊗-mono-right M₁ ω≤M₁) M

\end{code}
