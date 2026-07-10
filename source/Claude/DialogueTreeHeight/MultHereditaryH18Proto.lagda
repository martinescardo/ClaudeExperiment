PROTOTYPE (not in the tour, not depended on): a study of the rebase core for
the function-middle `S` combinator.

⚠ CORRECTION (2026-07-08): `fnmid-leaf-gen` below is FLAWED as a model of the
obstruction, and the conclusion it was written to support — that crediting a
function argument `2×` its budget closes the fn-middle `S` deficit — is FALSE.
The lemma models the *source* leaf with the `1×`-budget diagonal (`uδ = jφ +ℕ
jγ`, giving `2·jγ`) but pairs it with a `2×` *target* (`2·jγ`) — an
inconsistent mixing of the budget factor `m`. Under a *consistent* factor the
diagonal budget also scales: feeding the function-value `γ a` to `φ` charges
`m·jγ` into `uδ` (hence `jδ`), while the multiplier `Mδ` independently carries
`1·jγ` (from γ's `PackDom` bound on `γ a`'s multiplier, `Mkg ≤ bumpk jγ Mγ`,
which does not depend on `m`). So the source leaf is `(m+1)·jγ` and the target
is `m·jγ`: the deficit is `jγ` for EVERY `m` — scaling-invariant. The lemmas
still type-check (the arithmetic is real); they just do not model the actual
composition. The genuine obstruction: `γ a`'s budget `jγ` appears TWICE in the
leaf (as the value's budget cost AND as its multiplier's bump-count), but the
argument `kγ` supplies it once — the ordinal cost of a function-typed
intermediate result, unbeaten by any uniform budget/pool scaling. Kept as the
record of a wrong turn. The `2×` `HM*` line (`MultHereditaryHM…`) built on this
premise is likewise a documented dead end for the fn-middle goal.

The (retained) original rationale, for reference:
The function-middle `S` diagonal (`MultHereditaryH17`) is blocked at the
`pack2` composition by a `2·jγ`-vs-`1·jγ` leaf deficit: feeding the
function-value `γ a` to `φ` charges the argument budget `jγ` twice — once into
the diagonal's budget `jδ`, once as `jγ` bumps inside its multiplier `Mδ` — but
the flat-pool predicate credits a consumed function-argument only `1× jγ`.

Two facts reframe this (see the project note): (i) `bumpk` of any *finite*
count preserves `< ε₀`, so the budget's value is irrelevant to the `< ε₀`
goal — it only governs whether the composition inequalities hold; (ii) the
over-count in the current `mult-rebase` comes from composing *two* hypotheses
(budget-index `I3` and pool-base `I2`), each carrying the target budget.

This prototype validates the fix in isolation, without touching the tower:

* `mult-rebase-merged` — the reworked core. Fold the multiplier's bump-content
  into the budget index (multiplier-as-base, all bumps counted in `d`): then
  the leaf domination is a *single* `bumpk`-index chain resting on *one*
  pool-domination fact `bumpk a base ≤ bumpk b base′` (the `mult-absorb`
  shape), with no composition and hence no over-count.

* `fnmid-leaf` — the exact fn-middle leaf inequality (`τ = ι`) that FAILED
  under `1×` budget now CLOSES: the source leaf multiplier `bumpk jδ Mδ`
  (`jδ = (jφ +ℕ jγ) +ℕ 3`, `Mδ = bumpk (jγ +ℕ 3) base₀`, total `jφ +ℕ 2·jγ +ℕ 6`
  bumps over `base₀ = Mφ ⊗ (Mγ ⊗ ω)`) is dominated by the target
  `bumpk ((jφ +ℕ 8) +ℕ (jγ +ℕ jγ)) pool` — the output budget `jφ +ℕ 8` is
  `jγ`-FREE, and the argument budget is credited `2× = jγ +ℕ jγ`.

So the arithmetic core of the fix (doubled argument budget + merged
representation) is sound. The full tower rebuild (charge fn-args `2×` in
`MultHereditaryH`, rework `MultHereditaryH3`, re-verify `H2–H17`) is the
separate, larger step. The conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryH18Proto
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import Claude.BrouwerOrdinals.Order fe using (_≤_ ; ≤-trans ; _⊕_)
open import Claude.BrouwerOrdinals.Orbit fe using (ω ; _⊗_)
open import Claude.BrouwerOrdinals.MultBump fe using (bumpk ; bumpk-mono)
open import Claude.DialogueTreeHeight.MultHereditaryH fe using (_+ℕ_)
open import Claude.DialogueTreeHeight.MultHereditaryH2 fe
 using (bumpk-+ ; +ℕ-assoc ; +ℕ-comm)
open import Claude.DialogueTreeHeight.MultHereditaryH9 fe
 using (mult-absorb)
open import Claude.DialogueTreeHeight.MultHereditaryH10 fe
 using (le ; bumpk-le ; le-refl ; le-＝-left ; le-+ℕ-right)

\end{code}

The reworked rebase core. All bumps are counted in the budget `d`; a single
pool-domination fact `bumpk a base ≤ bumpk b base′` drives one `bumpk`-index
chain. No two-hypothesis composition, so no double-count of the argument
budget.

\begin{code}

mult-rebase-merged : (base base′ : 𝓑) (a b d Jt : ℕ)
                   → bumpk a base ≤ bumpk b base′
                   → le (d +ℕ b) Jt
                   → bumpk (d +ℕ a) base ≤ bumpk Jt base′
mult-rebase-merged base base′ a b d Jt H1 H2 =
 transport (λ z → z ≤ bumpk Jt base′) ((bumpk-+ d a base) ⁻¹)
   (≤-trans (bumpk-mono d H1)
     (transport (λ z → z ≤ bumpk Jt base′) (bumpk-+ d b base′)
       (bumpk-le base′ H2)))

\end{code}

The function-middle leaf, general in the result type. The `jγ`-content of
the source is exactly `2·jγ` (one `jγ` from the diagonal budget `jδ`, one
from the multiplier `Mδ`), sitting over a `jγ`-FREE overhead `s` (`s`
absorbs `jφ` and the `rbb τ` spine overhead, which is `jγ`-free for every
first-order `τ`). The claim: for ANY `jγ`-free output budget `j2` covering
`s +ℕ 5`, the source leaf `bumpk (s +ℕ 2·jγ +ℕ 3) base₀` is dominated by
`bumpk (j2 +ℕ 2·jγ) pool`. So the fix (credit function-args `2×`) closes the
whole first-order fn-middle `S` family, not just `τ = ι` — the output budget
stays `jγ`-free. Under the current `1×` budget the target would be
`bumpk (j2 +ℕ jγ) pool`, forcing `jγ` into the `jγ`-free `j2` — the
obstruction.

\begin{code}

fnmid-leaf-gen : (Mφ Mγ M2 : 𝓑) (s j2 jγ : ℕ)
               → Mφ ≤ (M2 ⊕ Mγ) → Mγ ≤ (M2 ⊕ Mγ) → ω ≤ (M2 ⊕ Mγ)
               → le (s +ℕ 5) j2
               → bumpk (((s +ℕ jγ) +ℕ jγ) +ℕ 3) (Mφ ⊗ (Mγ ⊗ ω))
                 ≤ bumpk (j2 +ℕ (jγ +ℕ jγ)) (M2 ⊕ Mγ)
fnmid-leaf-gen Mφ Mγ M2 s j2 jγ hφ hγ hω hj2 =
 mult-rebase-merged base₀ pool 3 5
   ((s +ℕ jγ) +ℕ jγ) (j2 +ℕ (jγ +ℕ jγ)) H1 H2
 where
  base₀ pool : 𝓑
  base₀ = Mφ ⊗ (Mγ ⊗ ω)
  pool  = M2 ⊕ Mγ

  H1 : bumpk 3 base₀ ≤ bumpk 5 pool
  H1 = mult-absorb Mφ Mγ pool 0 hφ hγ hω

  H2 : le (((s +ℕ jγ) +ℕ jγ) +ℕ 5) (j2 +ℕ (jγ +ℕ jγ))
  H2 = le-＝-left eqA (le-+ℕ-right (jγ +ℕ jγ) hj2)
   where
    eqA : (((s +ℕ jγ) +ℕ jγ) +ℕ 5) ＝ ((s +ℕ 5) +ℕ (jγ +ℕ jγ))
    eqA = ap (_+ℕ 5) (+ℕ-assoc s jγ jγ)
          ∙ +ℕ-assoc s (jγ +ℕ jγ) 5
          ∙ ap (s +ℕ_) (+ℕ-comm (jγ +ℕ jγ) 5)
          ∙ (+ℕ-assoc s 5 (jγ +ℕ jγ)) ⁻¹

\end{code}

The concrete `τ = ι` instance (`s = jφ +ℕ 3`, output budget `j2 = jφ +ℕ 8`):
the source `bumpk ((jφ +ℕ 2·jγ) +ℕ 6) base₀ = bumpk jδ Mδ` closes.

\begin{code}

fnmid-leaf-ι : (Mφ Mγ M2 : 𝓑) (jφ jγ : ℕ)
             → Mφ ≤ (M2 ⊕ Mγ) → Mγ ≤ (M2 ⊕ Mγ) → ω ≤ (M2 ⊕ Mγ)
             → bumpk ((((jφ +ℕ 3) +ℕ jγ) +ℕ jγ) +ℕ 3) (Mφ ⊗ (Mγ ⊗ ω))
               ≤ bumpk ((jφ +ℕ 8) +ℕ (jγ +ℕ jγ)) (M2 ⊕ Mγ)
fnmid-leaf-ι Mφ Mγ M2 jφ jγ hφ hγ hω =
 fnmid-leaf-gen Mφ Mγ M2 (jφ +ℕ 3) (jφ +ℕ 8) jγ hφ hγ hω
   (le-＝-left (+ℕ-assoc jφ 3 5) (le-refl (jφ +ℕ 8)))

\end{code}
