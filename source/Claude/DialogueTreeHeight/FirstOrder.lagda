The first-order recursor height bound, `< ε₀` (constructive).

This assembles the verified bricks into the recursor case of the
**first-order** theorem: the height of a ground iteration `iter' f x n` is
`< ε₀`, given

* the first-order **per-step increment**: each step of the orbit raises the
  height by at most the fixed code `ω^ω` (this is what the value-side
  Count/Magnitude analysis provides for a first-order `f` — finite
  magnitudes give finite ω-exponents, all absorbed into `ω^ω`); and
* that the **subterm heights** `height x` and `height n` are already `< ε₀`.

The proof is pure assembly:

* `DialogueTreeHeight.Orbit.height-iter-from-step` (the engine) turns the
  per-step increment into the explicit bound
  `height (iter' f x n) ≤ (height x ⊕ ω^ω ⊗ ω) ⊕ height n`;
* `DialogueTreeHeight.Epsilon0` supplies `ω^ω ⊗ ω < ε₀` and the additive
  `< ε₀` closure, collapsing that bound to `< ε₀`.

So the entire dialogue-specific and ordinal-arithmetic content of the
first-order recursor case is machine-checked here; what is **not** done is
the structural term induction that *discharges the three hypotheses* — that
every first-order `f` does present a fixed `ω^ω` per-step increment, and that
the subterm heights are `< ε₀` — which is sub-development (II) of
`dialogue-tree-height-frontier.md`. This module is the target that induction
lands on, and it shows the target is reached: the hypotheses are exactly the
honest interface between the (done) semantics and the (remaining) syntax.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.FirstOrder
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe
open import Claude.BrouwerOrdinals.Epsilon0 fe

\end{code}

The first-order recursor height bound. The increment `ω^ω` and the two
`< ε₀` hypotheses are the interface the term induction must supply.

\begin{code}

height-iter-<-ε₀
 : (f : B ℕ → B ℕ) (x : B ℕ)
 → ((k : ℕ) → height (iter f x (succ k)) ≤ (height (iter f x k) ⊕ ω^ ω))
 → (n : B ℕ)
 → height x < ε₀
 → height n < ε₀
 → height (kleisli-extension (iter f x) n) < ε₀
height-iter-<-ε₀ f x step n hx hn =
 ≤-trans (≤-S (height-iter-from-step f x (ω^ ω) step n)) bound-<-ε₀
 where
  bound-<-ε₀ : ((height x ⊕ ((ω^ ω) ⊗ ω)) ⊕ height n) < ε₀
  bound-<-ε₀ =
   ⊕-<-ε₀ (height x ⊕ ((ω^ ω) ⊗ ω)) (height n)
          (⊕-<-ε₀ (height x) ((ω^ ω) ⊗ ω) hx ω^ω⊗ω-<-ε₀)
          hn

\end{code}
