Design H, stage 2d(viii-a): the arithmetic obligations of `pack2`, verified
in isolation.

Assembling `pack2` (the middle `S` pack) means discharging several
`bumpk`-index and `rbb`-budget identities that mix the two argument budgets
`jφ , jγ` with fixed constants. These are the error-prone core; this module
proves them as standalone lemmas (with the clean fixed budget
`j₂ = 9 +ℕ jφ`, chosen so `rbb ι (3 +ℕ jφ) 5 ＝ j₂` — `eq-j2` — matching the
inner `ZCont-rebase` output), so the `pack2` plumbing can rest on checked
pieces rather than inline `_+ℕ_` gymnastics. The conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryH12
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.BrouwerOrdinals.MultBump fe using (bumpk)
open import Claude.DialogueTreeHeight.MultHereditaryH fe using (_+ℕ_)
open import Claude.DialogueTreeHeight.MultHereditaryH2 fe
 using (+ℕ-zero-right ; +ℕ-succ-right ; +ℕ-comm ; +ℕ-assoc ; rbb)
open import Claude.DialogueTreeHeight.MultHereditaryH10 fe
 using (le ; bumpk-le ; le-refl ; le-trans ; le-add-right ; le-add-left ;
        le-+ℕ-right ; le-＝-left ; le-＝-right)

\end{code}

The output-budget identity: the inner rebase produces `rbb ι (3 +ℕ jφ) 5`,
which equals the chosen fixed `j₂ = 9 +ℕ jφ`.

\begin{code}

eq-j2 : (jφ : ℕ) → rbb ι (3 +ℕ jφ) 5 ＝ (9 +ℕ jφ)
eq-j2 jφ = ap succ
             (+ℕ-assoc 3 jφ 5
              ∙ ap (3 +ℕ_) (+ℕ-comm jφ 5)
              ∙ (+ℕ-assoc 3 5 jφ) ⁻¹)

\end{code}

`5 ≤ 9 +ℕ jφ`, and the multiplier obligation `le 5 ((9 +ℕ jφ) +ℕ jγ)`.

\begin{code}

le-5-9 : (jφ : ℕ) → le 5 (9 +ℕ jφ)
le-5-9 jφ = (4 +ℕ jφ) , +ℕ-assoc 5 4 jφ

L-pm : (jφ jγ : ℕ) → le (5 +ℕ 0) ((9 +ℕ jφ) +ℕ (0 +ℕ jγ))
L-pm jφ jγ =
 le-＝-left (+ℕ-zero-right 5)
   (le-trans (le-5-9 jφ) (le-add-right (9 +ℕ jφ) jγ))

\end{code}

The budget obligation: the diagonal's budget `jδ = rbb ι ((2 +ℕ jγ) +ℕ jφ)
0` is dominated by `j₂ +ℕ jγ`. Since `jδ ＝ (3 +ℕ jφ) +ℕ jγ` (commuting the
argument budgets through the successor), this is `le ((3 +ℕ jφ) +ℕ jγ)
((9 +ℕ jφ) +ℕ jγ)`, a tail-preserved `le (3 +ℕ jφ) (9 +ℕ jφ)`.

\begin{code}

jδ-＝ : (jφ jγ : ℕ) → rbb ι ((2 +ℕ jγ) +ℕ jφ) 0 ＝ ((3 +ℕ jφ) +ℕ jγ)
jδ-＝ jφ jγ =
 ap succ (+ℕ-zero-right ((2 +ℕ jγ) +ℕ jφ))
 ∙ ap succ (+ℕ-assoc 2 jγ jφ ∙ ap (2 +ℕ_) (+ℕ-comm jγ jφ)
            ∙ (+ℕ-assoc 2 jφ jγ) ⁻¹)

le-3-9 : (jφ : ℕ) → le (3 +ℕ jφ) (9 +ℕ jφ)
le-3-9 jφ = 6 , (fwd ⁻¹)
 where
  fwd : ((3 +ℕ jφ) +ℕ 6) ＝ (9 +ℕ jφ)
  fwd = +ℕ-assoc 3 jφ 6
        ∙ ap (3 +ℕ_) (+ℕ-comm jφ 6)
        ∙ (+ℕ-assoc 3 6 jφ) ⁻¹

L-pj : (jφ jγ : ℕ)
     → le (rbb ι ((2 +ℕ jγ) +ℕ jφ) 0) ((9 +ℕ jφ) +ℕ (0 +ℕ jγ))
L-pj jφ jγ =
 le-＝-left (jδ-＝ jφ jγ)
   (le-+ℕ-right jγ (le-3-9 jφ))

\end{code}

The inner-rebase budget obligation `I3z`: source `jδ +ℕ 0`, target
`ur +ℕ (0 +ℕ jγ)` with `ur = 3 +ℕ jφ`, `JH′ = jγ`. Since `jδ ＝
(3 +ℕ jφ) +ℕ jγ = ur +ℕ jγ`, this is reflexivity up to the identity.

\begin{code}

L-I3z : (jφ jγ : ℕ)
      → le (rbb ι ((2 +ℕ jγ) +ℕ jφ) 0 +ℕ 0) ((3 +ℕ jφ) +ℕ (0 +ℕ jγ))
L-I3z jφ jγ =
 le-＝-left (+ℕ-zero-right (rbb ι ((2 +ℕ jγ) +ℕ jφ) 0) ∙ jδ-＝ jφ jγ)
   (le-refl ((3 +ℕ jφ) +ℕ jγ))

\end{code}

The `I1z` multiplier index `le 1 (((ur +ℕ 5) +ℕ (0 +ℕ jγ)))` — one bump for
the `ω ⊗ ω`, dominated by the large rebased index.

\begin{code}

L-I1z : (jφ jγ : ℕ) → le 1 (((3 +ℕ jφ) +ℕ 5) +ℕ (0 +ℕ jγ))
L-I1z jφ jγ = (((2 +ℕ jφ) +ℕ 5) +ℕ (0 +ℕ jγ)) , refl

\end{code}
