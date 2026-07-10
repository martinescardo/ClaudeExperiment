Super-linear orbit-closure: iterating the squaring map `b ↦ b ⊗ b` stays `< ε₀`.

The recursor half of the reframe needs the base transformer class to be
*orbit-closed*, and — as `MultHereditaryE` showed on the `S` side — that class
must reach beyond linear (`(b ⊕ c) ⊗ M`) growth to genuinely **super-linear**
transformers such as squaring. `Affine.double-orbit-<-ε₀` handles the *linear*
doubling `b ↦ b ⊕ b` (`= b ⊗ ι[2]`, whose orbit is `⊗ ω`). This module does the
super-linear case: the orbit of `b ↦ b ⊗ b` (degree two) is still `< ε₀`.

The key is that squaring only *adds one level* to the `ω`-exponent per step:
if `w ≤ ω^ b`, then `iter sq w k ≤ ω^(b ⊗ ι[2ᵏ])` — the exponent grows by the
same `⊗ ι[2ᵏ]` pattern the linear doubling used, but *inside* a single `ω`-power
(via the exponent homomorphism `ω^ x ⊗ ω^ x = ω^(x ⊕ x)`). Hence the supremum is
`ω^(b ⊗ ω) < ε₀`. This is exactly why squaring's orbit stays below `ε₀` while
*exponentiation's* (`b ↦ ω^ b`) reaches it: squaring moves the exponent by a
bounded multiple, exponentiation moves the code itself up a tower level.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.BrouwerOrdinals.MultSquareOrbit
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import Claude.BrouwerOrdinals.Order fe
open import Claude.BrouwerOrdinals.Orbit fe using (ι[_] ; ω ; _⊗_)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ω^_ ; Z-left-unit ; ω^-ι1 ; ω^-mono ;
        ⊗-mono-left ; ⊗-mono-right ; tower ; tower-<-ε₀ ; ω^-<-ε₀)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (ω^⊗ ; ⊗-<-ε₀)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊗-left-distrib ; ι-+-homo ; pow2)
open import Claude.BrouwerOrdinals.AffineClosure fe using (ι<ε₀)

\end{code}

The squaring map, and the per-step exponent bound: iterating it `k` times from
`w ≤ ω^ b` lands below `ω^(b ⊗ ι[2ᵏ])`. The successor step squares the bound and
merges the two equal `ω`-powers with `ω^⊗`, then rewrites the exponent using the
distributivity/`ι`-additivity that `Affine.double-orbit-≤` used.

\begin{code}

sq : 𝓑 → 𝓑
sq b = b ⊗ b

sq-orbit-≤ : (b w : 𝓑) → w ≤ ω^ b → (k : ℕ) → iter sq w k ≤ ω^ (b ⊗ ι[ pow2 k ])
sq-orbit-≤ b w w≤ zero =
 transport (λ z → w ≤ ω^ z) ((Z-left-unit b) ⁻¹) w≤
sq-orbit-≤ b w w≤ (succ k) =
 transport (λ z → iter sq w (succ k) ≤ z) eq step
 where
  E : 𝓑
  E = ω^ (b ⊗ ι[ pow2 k ])

  IH : iter sq w k ≤ E
  IH = sq-orbit-≤ b w w≤ k

  step : iter sq w (succ k) ≤ (E ⊗ E)
  step = ≤-trans (⊗-mono-left IH (iter sq w k)) (⊗-mono-right E IH)

  eq : (E ⊗ E) ＝ ω^ (b ⊗ ι[ pow2 (succ k) ])
  eq = ω^⊗ (b ⊗ ι[ pow2 k ]) (b ⊗ ι[ pow2 k ])
     ∙ ap ω^_ ( (⊗-left-distrib b ι[ pow2 k ] ι[ pow2 k ]) ⁻¹
              ∙ ap (b ⊗_) ((ι-+-homo (pow2 k) (pow2 k)) ⁻¹) )

\end{code}

Hence the orbit supremum is `≤ ω^(b ⊗ ω)`: each exponent `b ⊗ ι[2ᵏ]` is below
`b ⊗ ω`.

\begin{code}

sq-orbit-sup-≤ : (b w : 𝓑) → w ≤ ω^ b → L (λ k → iter sq w k) ≤ ω^ (b ⊗ ω)
sq-orbit-sup-≤ b w w≤ =
 ≤-L (λ k → ≤-trans (sq-orbit-≤ b w w≤ k)
                    (ω^-mono (⊗-mono-right b (≤-L-upper-bound ι[_] (pow2 k)))))

\end{code}

Every `w < ε₀` is below some `ω^ b` with `b < ε₀` (`w ≤ tower n = ω^(expo n)`).

\begin{code}

≤-S-self : (a : 𝓑) → a ≤ S a
≤-S-self Z     = ≤-Z
≤-S-self (S a) = ≤-S (≤-S-self a)
≤-S-self (L f) = ≤-L (λ n → ≤-trans (≤-S-self (f n)) (≤-S (≤-L-upper-bound f n)))

expo : ℕ → 𝓑
expo zero     = ι[ 1 ]
expo (succ m) = tower m

tower-≤-ω^expo : (n : ℕ) → tower n ≤ ω^ (expo n)
tower-≤-ω^expo zero     =
 transport (λ z → tower 0 ≤ z) (ω^-ι1 ⁻¹) (≤-refl (tower 0))
tower-≤-ω^expo (succ m) = ≤-refl (tower (succ m))

expo-<ε₀ : (n : ℕ) → expo n < ε₀
expo-<ε₀ zero     = ι<ε₀ 1
expo-<ε₀ (succ m) = tower-<-ε₀ m

w-≤-ω^ : (w : 𝓑) → w < ε₀ → Σ b ꞉ 𝓑 , (b < ε₀) × (w ≤ ω^ b)
w-≤-ω^ w (≤-ℓ n q) =
 expo n , expo-<ε₀ n , ≤-trans (≤-trans (≤-S-self w) q) (tower-≤-ω^expo n)

\end{code}

The payoff: the orbit of the (super-linear) squaring map, from a `< ε₀` start,
is `< ε₀`. So the base transformer class of the reframe can contain squaring —
super-linear growth — and remain orbit-closed, unlike `ω`-exponentiation.

\begin{code}

sq-orbit-<-ε₀ : (w : 𝓑) → w < ε₀ → L (λ k → iter sq w k) < ε₀
sq-orbit-<-ε₀ w w<ε₀ with w-≤-ω^ w w<ε₀
... | (b , b<ε₀ , w≤) =
 ≤-trans (≤-S (sq-orbit-sup-≤ b w w≤))
         (ω^-<-ε₀ (b ⊗ ω) (⊗-<-ε₀ b ω b<ε₀ (tower-<-ε₀ 0)))

\end{code}
