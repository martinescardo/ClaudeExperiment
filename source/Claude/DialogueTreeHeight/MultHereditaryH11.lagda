Design H, stage 2d(vii): the jγ-free-multiplier diagonal absorption — the
inequality that lets the `S`-diagonal pack *compose* into the outer packs.

`MultHereditaryH8`'s `packδ` (verified in isolation) parks the second
argument's budget in its *multiplier* `Mδ`, which — as the `pack2` analysis
showed — then cannot pass the outer rebase's pool hypothesis `I2` (no `+JH`
slot) with fixed slack. The resolution routes that budget through the
*budget* instead, keeping `Mδ = bumpk 3 (Mφ ⊗ (Mγ ⊗ ω))` **jγ-free**; then
`pack2`'s `I2` is `MultHereditaryH9.mult-absorb` at `n = 0` (constant slack
`5`), and the diagonal's `I1` needs, in place of the old `keyM`, the bound
verified here:

  `diag-absorb`: `((ω ⊗ bumpk n (Mγ ⊕ Z)) ⊗ ω) ≤ bumpk (2 +ℕ n) (Mφ ⊗ (Mγ ⊗ ω))`.

The `bumpk n (Mγ ⊕ Z)` on the left is exactly the multiplier of the
γ-value's bound (forced by γ's pack, `n = jγ`); this lemma absorbs it — and
the two trailing `ω` factors — into `2 + n` bumps of the jγ-free base, so
the diagonal's budget index (which carries `jγ`) covers it. Two `⊗-≤-bump`
steps, then `bumpk` composes. This is the sole new inequality of the
budget-routing resolution; with it and `mult-absorb`, both `packδ` (rebuilt
jγ-free) and `pack2` close. The conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryH11
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe using (ω ; _⊗_)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (⊗-mono-left ; ⊗-mono-right)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (x-≤-x⊗ ; y-≤-⊗)
open import Claude.BrouwerOrdinals.MultAffine fe using (ω-pos)
open import Claude.BrouwerOrdinals.MultBump fe
 using (bump ; bumpk ; bumpk-mono ; ≤-bump ; ⊗-≤-bump)
open import Claude.DialogueTreeHeight.MultHereditaryH fe using (_+ℕ_)
open import Claude.DialogueTreeHeight.MultHereditaryH2 fe
 using (bumpk-+ ; ≤-bumpk)

\end{code}

The absorption. `Mγ ⊕ Z` reduces to `Mγ` definitionally.

\begin{code}

diag-absorb : (Mφ Mγ : 𝓑) (n : ℕ) → S Z ≤ Mφ → S Z ≤ Mγ
            → ((ω ⊗ bumpk n (Mγ ⊕ Z)) ⊗ ω)
              ≤ bumpk (2 +ℕ n) (Mφ ⊗ (Mγ ⊗ ω))
diag-absorb Mφ Mγ n Mφ+ Mγ+ =
 transport (λ z → ((ω ⊗ bumpk n (Mγ ⊕ Z)) ⊗ ω) ≤ z)
           ((bumpk-+ 2 n base₀) ⁻¹)
           s2
 where
  base₀ : 𝓑
  base₀ = Mφ ⊗ (Mγ ⊗ ω)

  P0 : 𝓑
  P0 = bumpk n base₀

  Mγ≤base₀ : Mγ ≤ base₀
  Mγ≤base₀ = ≤-trans (x-≤-x⊗ Mγ ω ω-pos) (y-≤-⊗ Mφ (Mγ ⊗ ω) Mφ+)

  ω≤base₀ : ω ≤ base₀
  ω≤base₀ = ≤-trans (y-≤-⊗ Mγ ω Mγ+) (y-≤-⊗ Mφ (Mγ ⊗ ω) Mφ+)

  Bγ≤P0 : bumpk n (Mγ ⊕ Z) ≤ P0
  Bγ≤P0 = bumpk-mono n Mγ≤base₀

  ω≤P0 : ω ≤ P0
  ω≤P0 = ≤-trans ω≤base₀ (≤-bumpk n base₀)

  s1 : (ω ⊗ bumpk n (Mγ ⊕ Z)) ≤ bump P0
  s1 = ≤-trans (⊗-mono-left ω≤P0 (bumpk n (Mγ ⊕ Z)))
        (≤-trans (⊗-mono-right P0 Bγ≤P0) (⊗-≤-bump P0))

  s2 : ((ω ⊗ bumpk n (Mγ ⊕ Z)) ⊗ ω) ≤ bumpk 2 P0
  s2 = ≤-trans (⊗-mono-left s1 ω)
        (≤-trans (⊗-mono-right (bump P0) (≤-trans ω≤P0 (≤-bump P0)))
                 (⊗-≤-bump (bump P0)))

\end{code}

So the γ-value's multiplier (`n = jγ`) and the two `ω` factors are absorbed
into `2 + jγ` bumps of the jγ-free base — carried by the diagonal's budget
index `uδ = jγ +ℕ (jφ +ℕ 3)`. Combined with `MultHereditaryH9.mult-absorb`
(`n = 0` for the outer pool step) and the `MultHereditaryH10` index toolkit,
every arithmetic obligation of the jγ-free `packδ` and its composition into
`pack2` is now verified.
