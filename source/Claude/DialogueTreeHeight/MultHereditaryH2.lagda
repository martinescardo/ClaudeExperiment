Design H, stage 2a: the rebase arithmetic — the inequality layer for
re-basing Howard-tower bounds.

Every combinator pack of `MultHereditaryH`'s tower is proved by *re-basing*:
a `ZCont` bound obtained from an argument's pack (with its accumulators and
budget) must be converted into a bound under the consumer's pack. The
conversion is governed by four invariants, threaded along the argument
spine with two ℕ-parameters `u` (base budget) and `e` (pool slack):

  (I1) base:   `∀ w → (D w ⊕ (A w ⊕ c))
                  ≤ ((D′ w ⊕ (A′ w ⊕ c′)) ⊗ bumpk ((u + e) + JH′) (M′ ⊕ MH′))`
  (I2) pool:   `(M ⊕ MH) ≤ bumpk e (M′ ⊕ MH′)`   (raw pool, fixed slack)
  (I3) budget: `∀ P → bumpk (j + JH) P ≤ bumpk (u + JH′) P`  (semantic form)
  (I4) pos:    `ω ≤ (M′ ⊕ MH′)`

with the step discipline: a ground argument costs `u ↦ succ u` (the zone
extension `zdom-ext` pays `⊗ ω`, absorbed by one bump); a function argument
additionally costs `e ↦ succ e` (the pool extension pays one duplication).
The concluding pack budget is the spine-computed `rbb τ u e`. The chains at
the ground case are: (I3) then (I2) flatten the old bumps into
`bumpk ((u + e) + JH′)` of the new pool (`bumpk-+` and the ℕ-shuffle
`+ℕ-shuffle`), and the two factors merge by `⊗-≤-bump` — one more bump.
Crucially the pool substitution costs an *additive* budget shift only —
stating (I2) on the raw pool with explicit slack is what prevents the
bumps-of-bumps explosion that a bumped pool hypothesis would cause.

This module proves the whole inequality layer: ℕ-arithmetic for the
budgets, `bumpk` calculus (`bumpk-+`, `≤-bumpk`, `bumpk-pad`, `ω-≤-bump`,
`B-step`), the zone-extension lemma `zdom-ext`, the pool-extension lemma
`pool-ext`, and the budget function `rbb`. The rebase itself (the mutual
induction transcribing these along `ZCont`/`ZApply`) and the combinator
packs are the next stage; the conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryH2
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left ; ⊕-assoc)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right ;
        ⊕-increasing-right ; ω^-mono)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊗-assoc ; ⊕-increasing-left)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (x-≤-x⊗ ; SZ-⊗)
open import Claude.BrouwerOrdinals.MultAffine fe using (ω-pos)
open import Claude.DialogueTreeHeight.MultHereditaryFAff fe
 using (⊕-dup-≤-⊗ω ; ⊕-trip-≤-⊗ω)
open import Claude.BrouwerOrdinals.MultBump fe
 using (bump ; bumpk ; bump-mono ; bumpk-mono ; ≤-bump ; ⊗-≤-bump)
open import Claude.DialogueTreeHeight.MultHereditaryH fe
 using (_+ℕ_)

\end{code}

Budget arithmetic on ℕ.

\begin{code}

+ℕ-zero-right : (a : ℕ) → (a +ℕ 0) ＝ a
+ℕ-zero-right zero     = refl
+ℕ-zero-right (succ a) = ap succ (+ℕ-zero-right a)

+ℕ-succ-right : (a b : ℕ) → (a +ℕ succ b) ＝ succ (a +ℕ b)
+ℕ-succ-right zero     b = refl
+ℕ-succ-right (succ a) b = ap succ (+ℕ-succ-right a b)

+ℕ-comm : (a b : ℕ) → (a +ℕ b) ＝ (b +ℕ a)
+ℕ-comm zero     b = (+ℕ-zero-right b) ⁻¹
+ℕ-comm (succ a) b = ap succ (+ℕ-comm a b) ∙ (+ℕ-succ-right b a) ⁻¹

+ℕ-assoc : (a b c : ℕ) → ((a +ℕ b) +ℕ c) ＝ (a +ℕ (b +ℕ c))
+ℕ-assoc zero     b c = refl
+ℕ-assoc (succ a) b c = ap succ (+ℕ-assoc a b c)

+ℕ-shuffle : (a b c : ℕ) → ((a +ℕ b) +ℕ c) ＝ ((a +ℕ c) +ℕ b)
+ℕ-shuffle a b c =
 +ℕ-assoc a b c ∙ ap (a +ℕ_) (+ℕ-comm b c) ∙ (+ℕ-assoc a c b) ⁻¹

\end{code}

The `bumpk` calculus: composition, inflationarity, padding, and the
`ω`-floor of a bump.

\begin{code}

bumpk-+ : (a b : ℕ) (P : 𝓑) → bumpk (a +ℕ b) P ＝ bumpk a (bumpk b P)
bumpk-+ zero     b P = refl
bumpk-+ (succ a) b P = ap bump (bumpk-+ a b P)

≤-bumpk : (k : ℕ) (P : 𝓑) → P ≤ bumpk k P
≤-bumpk zero     P = ≤-refl P
≤-bumpk (succ k) P = ≤-trans (≤-bumpk k P) (≤-bump (bumpk k P))

bumpk-pad : (a d : ℕ) (P : 𝓑) → bumpk a P ≤ bumpk (a +ℕ d) P
bumpk-pad a d P =
 transport (λ z → bumpk a P ≤ z) ((bumpk-+ a d P) ⁻¹)
           (bumpk-mono a (≤-bumpk d P))

ω-≤-bump : (P : 𝓑) → S Z ≤ P → ω ≤ bump P
ω-≤-bump P P+ =
 transport (λ z → z ≤ bump P) (SZ-⊗ ω)
  (ω^-mono (≤-trans ω-pos
             (≤-trans (x-≤-x⊗ ω P P+) (x-≤-x⊗ (ω ⊗ P) ω ω-pos))))

ω-≤-bumpk : (k : ℕ) (P : 𝓑) → ω ≤ P → ω ≤ bumpk k P
ω-≤-bumpk k P h = ≤-trans h (≤-bumpk k P)

\end{code}

Absorbing a trailing `⊗ ω` into one bump: for a pool at or above `ω`, the
`⊗ ω` a zone-extension costs is dominated by squaring, hence by one bump.

\begin{code}

B-step : (k : ℕ) (P : 𝓑) → ω ≤ P
       → (bumpk k P ⊗ ω) ≤ bumpk (succ k) P
B-step k P h =
 ≤-trans (⊗-mono-right (bumpk k P) (ω-≤-bumpk k P h))
         (⊗-≤-bump (bumpk k P))

\end{code}

The zone-extension lemma: adding the same summand `X` to both accumulators
preserves the base domination at the cost of `⊗ ω` — three summands, each
below the extended zone times the old multiplier, packed by the triple
absorption.

\begin{code}

zdom-ext : (D D′ A A′ X : 𝓑 → 𝓑) (c c′ B : 𝓑)
         → S Z ≤ B
         → ((w : 𝓑) → (D w ⊕ (A w ⊕ c)) ≤ ((D′ w ⊕ (A′ w ⊕ c′)) ⊗ B))
         → (w : 𝓑) → (D w ⊕ ((A w ⊕ X w) ⊕ c))
                      ≤ ((D′ w ⊕ ((A′ w ⊕ X w) ⊕ c′)) ⊗ (B ⊗ ω))
zdom-ext D D′ A A′ X c c′ B B+ h w =
 transport (λ z → z ≤ (Y ⊗ (B ⊗ ω))) (lhs-eq ⁻¹)
           (transport (λ z → HX ≤ z) (⊗-assoc Y B ω) main)
 where
  H R Y : 𝓑
  H = D w ⊕ A w
  R = D′ w ⊕ (A′ w ⊕ c′)
  Y = D′ w ⊕ ((A′ w ⊕ X w) ⊕ c′)

  HX : 𝓑
  HX = (H ⊕ X w) ⊕ c

  lhs-eq : (D w ⊕ ((A w ⊕ X w) ⊕ c)) ＝ HX
  lhs-eq = ap (D w ⊕_) (⊕-assoc (A w) (X w) c)
           ∙ (⊕-assoc (D w) (A w) (X w ⊕ c)) ⁻¹
           ∙ (⊕-assoc (D w ⊕ A w) (X w) c) ⁻¹

  hyp : (H ⊕ c) ≤ (R ⊗ B)
  hyp = transport (λ z → z ≤ (R ⊗ B)) ((⊕-assoc (D w) (A w) c) ⁻¹) (h w)

  R≤Y : R ≤ Y
  R≤Y = transport (λ z → R ≤ (D′ w ⊕ z)) ((⊕-assoc (A′ w) (X w) c′) ⁻¹)
         (⊕-mono-right (D′ w)
           (⊕-mono-right (A′ w) (⊕-increasing-left (X w) c′)))

  X≤Y : X w ≤ Y
  X≤Y = ≤-trans (⊕-increasing-left (A′ w) (X w))
         (≤-trans (⊕-increasing-right (A′ w ⊕ X w) c′)
                  (⊕-increasing-left (D′ w) ((A′ w ⊕ X w) ⊕ c′)))

  H≤ : H ≤ (Y ⊗ B)
  H≤ = ≤-trans (⊕-increasing-right H c)
        (≤-trans hyp (⊗-mono-left R≤Y B))

  c≤ : c ≤ (Y ⊗ B)
  c≤ = ≤-trans (⊕-increasing-left H c)
        (≤-trans hyp (⊗-mono-left R≤Y B))

  main : HX ≤ ((Y ⊗ B) ⊗ ω)
  main = ≤-trans
          (≤-trans
            (⊕-mono-left (⊕-mono-left H≤ (X w)) c)
            (≤-trans
              (⊕-mono-left (⊕-mono-right (Y ⊗ B)
                             (≤-trans X≤Y (x-≤-x⊗ Y B B+))) c)
              (⊕-mono-right ((Y ⊗ B) ⊕ (Y ⊗ B)) c≤)))
          (transport (λ z → z ≤ ((Y ⊗ B) ⊗ ω))
                     ((⊕-assoc (Y ⊗ B) (Y ⊗ B) (Y ⊗ B)) ⁻¹)
                     (⊕-trip-≤-⊗ω (Y ⊗ B)))

\end{code}

The pool-extension lemma: joining the same multiplier `mh` to both pools
preserves the pool domination at the cost of one slack unit (a duplication
absorbed by one bump). Stated in the re-associated form the fn-arg clause
of `ZApply` produces.

\begin{code}

pool-ext : (Mo P mh : 𝓑) (e : ℕ)
         → ω ≤ P
         → Mo ≤ bumpk e P
         → (Mo ⊕ mh) ≤ bumpk (succ e) (P ⊕ mh)
pool-ext Mo P mh e Pω h =
 ≤-trans (≤-trans (⊕-mono-left Mo≤Q mh) (⊕-mono-right Q mh≤Q))
         (≤-trans (⊕-dup-≤-⊗ω Q)
                  (B-step e (P ⊕ mh)
                    (≤-trans Pω (⊕-increasing-right P mh))))
 where
  Q : 𝓑
  Q = bumpk e (P ⊕ mh)

  Mo≤Q : Mo ≤ Q
  Mo≤Q = ≤-trans h (bumpk-mono e (⊕-increasing-right P mh))

  mh≤Q : mh ≤ Q
  mh≤Q = ≤-trans (⊕-increasing-left P mh) (≤-bumpk e (P ⊕ mh))

\end{code}

The concluding pack-budget of a rebase, computed along the spine: one bump
per argument, one extra slack unit per function argument, and one final
bump for merging the base and pool factors at ground.

\begin{code}

rbb : type → ℕ → ℕ → ℕ
rbb ι               u e = succ (u +ℕ e)
rbb (ι ⇒ τ)         u e = rbb τ (succ u) e
rbb ((σ₁ ⇒ σ₂) ⇒ τ) u e = rbb τ (succ u) (succ e)

\end{code}
