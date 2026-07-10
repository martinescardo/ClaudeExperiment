Design H, stage 2d(vi): the `bumpk`-index monotonicity toolkit — the
natural-number `≤` bookkeeping the outer `S` packs (`pack2`, `packS`) run
on.

Every `PackDom` obligation of the outer packs reduces, after the
verified multiplicative step (`MultHereditaryH9.mult-absorb`) and the
zone/budget increasing-chains, to a *`bumpk`-index inequality*: `bumpk a P ≤
bumpk b P` for naturals `a ≤ b` built from `_+ℕ_` of the argument budgets
and fixed constants. This module isolates that bookkeeping as a small
order-theory of a `Σ`-based `≤` on `ℕ` (`le a b = Σ d , b ＝ a +ℕ d`) with
the closure properties the packs use — reflexivity, transitivity, adding a
constant on either side, and the commuting rearrangement `le a b →
le (a +ℕ c) (b +ℕ c)` — and the bridge `bumpk-le : le a b → bumpk a P ≤
bumpk b P` (via `bumpk-pad`). With this, an index obligation is discharged
by exhibiting the slack `d` and an `_+ℕ_` identity, keeping the pack proofs
free of inline transport chains. The conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryH10
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.BrouwerOrdinals.MultBump fe using (bumpk)
open import Claude.DialogueTreeHeight.MultHereditaryH fe using (_+ℕ_)
open import Claude.DialogueTreeHeight.MultHereditaryH2 fe
 using (+ℕ-zero-right ; +ℕ-succ-right ; +ℕ-comm ; +ℕ-assoc ; bumpk-pad)

\end{code}

The `Σ`-based order and the `bumpk` bridge.

\begin{code}

le : ℕ → ℕ → 𝓤₀ ̇
le a b = Σ d ꞉ ℕ , b ＝ (a +ℕ d)

bumpk-le : {a b : ℕ} (P : 𝓑) → le a b → bumpk a P ≤ bumpk b P
bumpk-le {a} {b} P (d , e) =
 transport (λ m → bumpk a P ≤ bumpk m P) (e ⁻¹) (bumpk-pad a d P)

\end{code}

Order structure.

\begin{code}

le-refl : (a : ℕ) → le a a
le-refl a = 0 , ((+ℕ-zero-right a) ⁻¹)

le-trans : {a b c : ℕ} → le a b → le b c → le a c
le-trans {a} {b} {c} (d , e) (d′ , e′) =
 (d +ℕ d′) , (e′ ∙ ap (_+ℕ d′) e ∙ +ℕ-assoc a d d′)

le-add-right : (a c : ℕ) → le a (a +ℕ c)
le-add-right a c = c , refl

le-add-left : (c a : ℕ) → le a (c +ℕ a)
le-add-left c a = c , (+ℕ-comm c a)

\end{code}

The commuting rearrangement: adding the same constant on the right of both
sides preserves the order (used to carry the argument's budget `jγ` as a
tail through the pack indices).

\begin{code}

le-+ℕ-right : {a b : ℕ} (c : ℕ) → le a b → le (a +ℕ c) (b +ℕ c)
le-+ℕ-right {a} {b} c (d , e) =
 d , (ap (_+ℕ c) e
      ∙ +ℕ-assoc a d c
      ∙ ap (a +ℕ_) (+ℕ-comm d c)
      ∙ (+ℕ-assoc a c d) ⁻¹)

le-+ℕ-left : {a b : ℕ} (c : ℕ) → le a b → le (c +ℕ a) (c +ℕ b)
le-+ℕ-left {a} {b} c (d , e) =
 d , (ap (c +ℕ_) e ∙ (+ℕ-assoc c a d) ⁻¹)

\end{code}

Rewriting the index along an `_+ℕ_` identity (e.g. erasing a `+ℕ 0`).

\begin{code}

le-＝-left : {a a′ b : ℕ} → a ＝ a′ → le a′ b → le a b
le-＝-left refl h = h

le-＝-right : {a b b′ : ℕ} → b′ ＝ b → le a b′ → le a b
le-＝-right refl h = h

\end{code}
