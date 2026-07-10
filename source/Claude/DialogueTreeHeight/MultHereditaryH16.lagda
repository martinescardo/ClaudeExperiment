Design H, stage 2d(x-a): the function-middle `I2` absorption — the new
arithmetic of the `S`-diagonal at a *function-typed* middle `σ`.

At a ground middle (`MultHereditaryH8`), the γ-value fed to `φ`'s slot is a
`GFun` bounded by a single `⊗ Bγ` term. At a *function* middle, the γ-value
is a `𝕂 σ` whose *multiplier* `kmult` enters the diagonal's pool, bounded —
via γ's `PackDom` (the tower predicate's constraining clause) — by
`bumpk jγ Mγ`. The diagonal's rebase hypothesis `I2` must then absorb
`Mφ ⊕ (that multiplier)` into the jγ-free `Mδ = bumpk 3 (Mφ ⊗ (Mγ ⊗ ω))`,
paying `jγ + 2` in the *budget* (rebase slack `e`), keeping `Mδ` jγ-free so
the outer packs still close at constant slack. `fnmid-I2` verifies exactly
this. The conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryH16
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe
 using (ω ; _⊗_ ; ⊕-mono-left)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (x-≤-x⊗ ; y-≤-⊗)
open import Claude.BrouwerOrdinals.MultAffine fe using (ω-pos)
open import Claude.DialogueTreeHeight.MultHereditaryFAff fe
 using (⊕-dup-≤-⊗ω)
open import Claude.BrouwerOrdinals.MultBump fe
 using (bump ; bumpk ; bumpk-mono ; ≤-bump ; ⊗-≤-bump)
open import Claude.DialogueTreeHeight.MultHereditaryH fe using (_+ℕ_)
open import Claude.DialogueTreeHeight.MultHereditaryH2 fe
 using (+ℕ-zero-right ; +ℕ-succ-right ; +ℕ-assoc ; bumpk-+ ; ≤-bumpk)
open import Claude.DialogueTreeHeight.MultHereditaryH4 fe
 using (⊕-Z-left)
open import Claude.DialogueTreeHeight.MultHereditaryH10 fe
 using (le ; bumpk-le ; le-＝-left ; le-＝-right)

\end{code}

The absorption. `M` is the γ-value's multiplier (bounded via `PackDom` by
`bumpk n (Mγ ⊕ Z)`, `n = jγ`); the result lands in `bumpk (n +ℕ 2)` of the
jγ-free base.

\begin{code}

fnmid-I2 : (Mφ Mγ M : 𝓑) (n : ℕ) → S Z ≤ Mφ → S Z ≤ Mγ
         → M ≤ bumpk n (Mγ ⊕ Z)
         → (Mφ ⊕ M) ≤ bumpk (n +ℕ 2) (bumpk 3 (Mφ ⊗ (Mγ ⊗ ω)))
fnmid-I2 Mφ Mγ M n Mφ+ Mγ+ hM =
 ≤-trans Mφ⊕M≤
   (transport (λ z → bump P0 ≤ z) (bumpk-+ (n +ℕ 2) 3 base₀)
              (bumpk-le base₀ le′))
 where
  base₀ : 𝓑
  base₀ = Mφ ⊗ (Mγ ⊗ ω)
  P0 : 𝓑
  P0 = bumpk n base₀

  Mγω+ : S Z ≤ (Mγ ⊗ ω)
  Mγω+ = ≤-trans ω-pos (y-≤-⊗ Mγ ω Mγ+)
  Mφ≤base₀ : Mφ ≤ base₀
  Mφ≤base₀ = x-≤-x⊗ Mφ (Mγ ⊗ ω) Mγω+
  Mγ≤base₀ : Mγ ≤ base₀
  Mγ≤base₀ = ≤-trans (x-≤-x⊗ Mγ ω ω-pos) (y-≤-⊗ Mφ (Mγ ⊗ ω) Mφ+)
  ω≤base₀ : ω ≤ base₀
  ω≤base₀ = ≤-trans (y-≤-⊗ Mγ ω Mγ+) (y-≤-⊗ Mφ (Mγ ⊗ ω) Mφ+)

  Mφ≤P0 : Mφ ≤ P0
  Mφ≤P0 = ≤-trans Mφ≤base₀ (≤-bumpk n base₀)
  ω≤P0 : ω ≤ P0
  ω≤P0 = ≤-trans ω≤base₀ (≤-bumpk n base₀)
  M≤P0 : M ≤ P0
  M≤P0 = ≤-trans hM (bumpk-mono n Mγ≤base₀)

  Mφ⊕M≤ : (Mφ ⊕ M) ≤ bump P0
  Mφ⊕M≤ = ≤-trans (⊕-mono-left Mφ≤P0 M)
           (≤-trans (⊕-mono-right P0 M≤P0)
             (≤-trans (⊕-dup-≤-⊗ω P0)
               (≤-trans (⊗-mono-right P0 ω≤P0) (⊗-≤-bump P0))))

  le′ : le (succ n) ((n +ℕ 2) +ℕ 3)
  le′ = le-＝-right ((+ℕ-assoc n 2 3) ⁻¹) (4 , +ℕ-succ-right n 4)

\end{code}
