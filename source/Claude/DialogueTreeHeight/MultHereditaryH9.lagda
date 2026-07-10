Design H, stage 2d(v): the outer-pack multiplier-absorption lemma — the key
inequality of `pack2`/`packS` for the `S` combinator, verified.

`MultHereditaryH8` built the `S`-diagonal pack `packδ`, whose multiplier
`Mδ = bumpk 3 (Mφ ⊗ (Bγ ⊗ ω))` carries the second argument's budget inside
`Bγ = bumpk jγ Mγ`. The outer packs (`pack2`, consuming `kγ`; `packS`,
consuming `kφ`) must, in their `PackDom` multiplier clause, dominate this
`Mδ` by `bumpk (j₂ + jγ) pool` where `pool` contains `Mφ`, `Mγ` and `ω`.
This module verifies exactly that domination:

  `mult-absorb`: with `Mφ , Mγ ≤ pool` and `ω ≤ pool`,
    `bumpk 3 (Mφ ⊗ (bumpk n (Mγ ⊕ Z) ⊗ ω)) ≤ bumpk (5 +ℕ n) pool`.

The proof floods everything below `pool`, so the base becomes `P⊗(P⊗P)` with
`P = bumpk n pool`, absorbed by two `⊗-≤-bump` steps into `bumpk 2 P`, then
the outer `bumpk 3` composes to `bumpk 5 P = bumpk (5 + n) pool`. So the
outer packs cost a *fixed* five bumps over the argument's budget — the
multiplier domination the full `GoodH-S` needs closes with `j₂ ≥ 5`
(plus `jφ` for the budget clause). The zone and budget clauses of the outer
packs are routine (increasing-chains and `bumpk-pad`); this multiplicative
step was the one that had to be checked. The conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryH9
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe using (ω ; _⊗_)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (⊗-mono-left ; ⊗-mono-right)
open import Claude.BrouwerOrdinals.MultBump fe
 using (bump ; bumpk ; bumpk-mono ; ≤-bump ; ⊗-≤-bump)
open import Claude.DialogueTreeHeight.MultHereditaryH fe using (_+ℕ_)
open import Claude.DialogueTreeHeight.MultHereditaryH2 fe
 using (bumpk-+ ; ≤-bumpk)

\end{code}

A product of three copies of `X` is below `bumpk 2 X` — two absorptions.

\begin{code}

⊗³-≤-bumpk2 : (X : 𝓑) → (X ⊗ (X ⊗ X)) ≤ bumpk 2 X
⊗³-≤-bumpk2 X =
 ≤-trans (⊗-mono-right X (⊗-≤-bump X))
   (≤-trans (⊗-mono-left (≤-bump X) (bump X))
            (⊗-≤-bump (bump X)))

\end{code}

The absorption lemma. `⊕ Z` on the right of `Mγ` reduces definitionally.

\begin{code}

mult-absorb : (Mφ Mγ pool : 𝓑) (n : ℕ)
            → Mφ ≤ pool → Mγ ≤ pool → ω ≤ pool
            → bumpk 3 (Mφ ⊗ (bumpk n (Mγ ⊕ Z) ⊗ ω)) ≤ bumpk (5 +ℕ n) pool
mult-absorb Mφ Mγ pool n hφ hγ hω =
 transport (λ z → bumpk 3 (Mφ ⊗ (bumpk n (Mγ ⊕ Z) ⊗ ω)) ≤ z)
           (idx ⁻¹)
           (bumpk-mono 3 base≤)
 where
  P : 𝓑
  P = bumpk n pool

  Mφ≤P : Mφ ≤ P
  Mφ≤P = ≤-trans hφ (≤-bumpk n pool)

  ω≤P : ω ≤ P
  ω≤P = ≤-trans hω (≤-bumpk n pool)

  Bγ≤P : bumpk n (Mγ ⊕ Z) ≤ P
  Bγ≤P = bumpk-mono n hγ

  base≤ : (Mφ ⊗ (bumpk n (Mγ ⊕ Z) ⊗ ω)) ≤ bumpk 2 P
  base≤ = ≤-trans (⊗-mono-left Mφ≤P (bumpk n (Mγ ⊕ Z) ⊗ ω))
           (≤-trans (⊗-mono-right P (⊗-mono-left Bγ≤P ω))
             (≤-trans (⊗-mono-right P (⊗-mono-right P ω≤P))
                      (⊗³-≤-bumpk2 P)))

  idx : bumpk (5 +ℕ n) pool ＝ bumpk 3 (bumpk 2 P)
  idx = bumpk-+ 5 n pool ∙ bumpk-+ 3 2 (bumpk n pool)

\end{code}

So `bumpk (5 +ℕ n) pool ＝ bumpk 3 (bumpk 2 (bumpk n pool))` since
`5 +ℕ n = 3 +ℕ (2 +ℕ n)` and `bumpk` composes (`bumpk-+`). The outer
pack's multiplier obligation is thereby discharged uniformly — five bumps
above the consumed argument's budget.
