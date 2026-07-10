From a per-step height increment to an orbit bound (constructive).

This module is the machine-checked *engine* of the bridge lemma (B) in the
two-component analysis (`dialogue-tree-height-two-component.md`,
`…-howard-build.md` Lemma R3): the precise sense in which **"depth cannot
bootstrap"**. The pure ordinal arithmetic it rests on — `ω`, `_⊗_`, the
fixed-increment orbit engine (`orbit-uniform`, `orbit-sup-≤`) — is now
factored out into `Claude.BrouwerOrdinals.Orbit` (re-exported below). What remains
here is the dialogue-tree reading:

  if each step of the orbit increases the height by at most a *fixed* code
  `c` — `height (fᵏ⁺¹ x) ≤ height (fᵏ x) ⊕ c` — then the whole orbit is
  bounded by `height x ⊕ (c ⊗ ω)`, and hence so is the oracle-driven
  iteration `iter' f x n`.

This is exactly the linearity at the heart of the ε₀ conjecture: a
per-application increment that **does not depend on the current depth**
`height (fᵏ x)` (only on a fixed `c`, read off from values/answers) forces
the orbit supremum up by only one factor of `ω`, never an exponential in the
depth. The increment `c` is an explicit hypothesis — never a postulate —
just as the orbit bound was a hypothesis in the conditional module.

The first-order reading: for a first-order `f` the per-step increment is
`c = ω^ω`, so the orbit sup is `≤ height x ⊕ (ω^ω ⊗ ω) = height x ⊕ ω^{ω+1}
< ε₀`. Identifying `c` with `ω^ω` for a *closed* first-order term is the
typed structural induction, deferred; that is the only remaining gap at
first order, and this engine is what it feeds.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.Orbit
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Conditional fe
open import Claude.BrouwerOrdinals.Orbit fe public

\end{code}

The payoff: an **unconditional** height bound for the ground iteration
`iter' f x n = kleisli-extension (iter f x) n`, given only a fixed per-step
height increment `c` for `f` along its orbit. Combining the engine
(`orbit-uniform`, giving the uniform orbit bound `height x ⊕ (c ⊗ ω)`) with
the conditional recursor bound yields

  `height (iter' f x n) ≤ (height x ⊕ (c ⊗ ω)) ⊕ height n`.

For a first-order `f` one takes `c = ω^ω`, whence the bound is
`height x ⊕ ω^{ω+1} ⊕ height n < ε₀` once `x, n` are closed.

\begin{code}

height-iter-from-step
 : (f : B ℕ → B ℕ) (x : B ℕ) (c : 𝓑)
 → ((k : ℕ) → height (iter f x (succ k)) ≤ (height (iter f x k) ⊕ c))
 → (n : B ℕ)
 → height (kleisli-extension (iter f x) n)
   ≤ ((height x ⊕ (c ⊗ ω)) ⊕ height n)
height-iter-from-step f x c step n =
 height-iter-≤-orbit-bound f x (height x ⊕ (c ⊗ ω))
  (orbit-uniform (λ k → height (iter f x k)) c step)
  n

\end{code}
