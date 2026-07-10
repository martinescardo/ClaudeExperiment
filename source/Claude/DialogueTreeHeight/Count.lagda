Counts and magnitudes for dialogue-tree heights (constructive).

This file formalises the "Count Lemma" from the two-component analysis
(`EffectfulForcing/DialogueTreeHeight/dialogue-tree-height-howard-build.md`, Lemmas R1 and
R-Count). The point is the defect found in the height-only majorant: in

    iter' f x n = kleisli-extension (iter f x) n   (at ground type),

the iteration performed at a leaf `η k` of the count `n` is `f` applied `k`
times, where `k` is the leaf *value*. The height `h(η k) = 0` for every
`k`, so height alone cannot see the count. The magnitude — a bound on the
leaf values — is what controls it.

We track magnitude by the predicate `values-≤ M d` ("every leaf value of
`d` is `≤ M`") and prove the count-sensitive grafting bound: to majorize
`kleisli-extension g d` it is enough to bound `height (g k)` for the
finitely many `k ≤ M` that can occur, rather than for all `k`. This is the
constructive, machine-checked core of the count-aware recursor.

Everything reuses the constructive Brouwer-code development.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.Count
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import Claude.DialogueTreeHeight.Constructive fe

\end{code}

A self-contained order on the natural numbers (to avoid name clashes with
the Brouwer-code order `_≤_`).

\begin{code}

_≤ℕ_ : ℕ → ℕ → 𝓤₀ ̇
zero   ≤ℕ n      = 𝟙
succ m ≤ℕ zero   = 𝟘
succ m ≤ℕ succ n = m ≤ℕ n

\end{code}

The magnitude predicate: every leaf value of `d` is `≤ M`. (Trees built
with `generic`, i.e. using the oracle, satisfy this for no finite `M` —
their leaf values are unbounded — which is exactly why the oracle is the
sole source of unbounded counts.)

\begin{code}

values-≤ : ℕ → B ℕ → 𝓤₀ ̇
values-≤ M (η n)   = n ≤ℕ M
values-≤ M (β φ i) = (j : ℕ) → values-≤ M (φ j)

\end{code}

The Count Lemma (height part). If the count tree `d` has all leaf values
`≤ M`, then to bound the height of the graft `kleisli-extension g d` it
suffices to bound `height (g k)` for `k ≤ M`. Compare
`height-kleisli-extension` in the constructive file, whose hypothesis
quantifies over *all* `k`; here we only need the values that occur.

\begin{code}

height-kleisli-extension-≤
 : (g : ℕ → B ℕ) (b : 𝓑) (M : ℕ)
 → ((k : ℕ) → k ≤ℕ M → height (g k) ≤ b)
 → (d : B ℕ) → values-≤ M d
 → height (kleisli-extension g d) ≤ (b ⊕ height d)
height-kleisli-extension-≤ g b M ϕ (η k)   v = ϕ k v
height-kleisli-extension-≤ g b M ϕ (β φ i) v =
 ≤-L-mono (λ j → ≤-S (height-kleisli-extension-≤ g b M ϕ (φ j) (v j)))

\end{code}

Specialisation to iteration: `iter f x k = fᵏ x`, so for a count tree `n`
with values `≤ M`, the height of the ground iteration is bounded using only
the iterates `fᵏ x` for `k ≤ M`.

\begin{code}

height-iter-bounded
 : (f : B ℕ → B ℕ) (x : B ℕ) (b : 𝓑) (M : ℕ)
 → ((k : ℕ) → k ≤ℕ M → height (iter f x k) ≤ b)
 → (n : B ℕ) → values-≤ M n
 → height (kleisli-extension (iter f x) n) ≤ (b ⊕ height n)
height-iter-bounded f x = height-kleisli-extension-≤ (iter f x)

\end{code}

Magnitude propagation for the successor (`succ' = B-functor succ`):
relabelling by `succ` raises the value bound by one. This is the
machine-checked form of "Succ increments magnitude" (Lemma S+).

\begin{code}

values-≤-B-functor-succ
 : (M : ℕ) (d : B ℕ)
 → values-≤ M d
 → values-≤ (succ M) (B-functor succ d)
values-≤-B-functor-succ M (η n)   v = v
values-≤-B-functor-succ M (β φ i) v =
 λ j → values-≤-B-functor-succ M (φ j) (v j)

\end{code}
