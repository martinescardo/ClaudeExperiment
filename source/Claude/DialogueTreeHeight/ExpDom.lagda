PROTOTYPE (not in the tour, not depended on): the **exponent-explicit** ground
layer of the squaring-closed class — `MultDominated.MDom` with its multiplier
pinned to the form `ω^ β`, exposing the exponent `β` so the two closures that
matter become *affine on `β`*.

Design note: `dialogue-tree-height-decoupling.md`. `MDomSquareOrbit` closed the
ground self-composition orbit with an opaque `ValidMult` multiplier. The
hereditary lift (obligation 3) needs the multiplier's transformation under
composition and self-composition to be TRACKABLE affinely; the `ω^(–)` functor
supplies exactly that. Writing the multiplier as `ω^ β`:

* **composition** `ω^ βψ ⊗ ω^ βφ = ω^ (βψ ⊕ βφ)` (`OmegaPoly.ω^⊗`) — the exponent
  ADDS (`ExpDom-∘`);
* **self-composition orbit** `ω^ β ⊗ ω^ β = ω^ (β ⊕ β)`, iterated gives exponent
  `β ⊗ ι[2ᵏ]`, sup `β ⊗ ω` (`MultSquareOrbit.sq-orbit-≤`) — the exponent
  DOUBLING-ORBITS (`ExpDom-sq-orbit`).

Both are affine maps on `β`, and the affine class on `β` is closed under both.
This is the arithmetic keystone of the two-tier design: exponents live in the
(already-built) affine world, `ω^(–)` transports additive→multiplicative. The
hereditary transformer clause and its fundamental theorem are the development
this underpins; the conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.ExpDom
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import Claude.BrouwerOrdinals.Order fe
 using (_≤_ ; _⊕_ ; ≤-refl ; ≤-trans ; ≤-L ; ≤-L-upper-bound)
open import Claude.BrouwerOrdinals.Orbit fe using (ι[_] ; ω ; _⊗_)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ω^_ ; ω^-mono ; ω^-<-ε₀ ; one-≤-ω^ ;
        ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right ; ⊕-<-ε₀ ; tower-<-ε₀)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (⊗-<-ε₀ ; ω^⊗)
open import Claude.BrouwerOrdinals.Affine fe
 using (pow2 ; double ; double-orbit-<-ε₀ ; ⊕-increasing-left)
open import Claude.BrouwerOrdinals.AffineClosure fe using (x-≤-x⊗)
open import Claude.BrouwerOrdinals.MultAffine fe using (ω-pos ; dbl-ω^)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; MDom ; MDom-∘ ; MDom-app ; validMult-⊗)
open import Claude.BrouwerOrdinals.MultSquareOrbit fe using (sq ; sq-orbit-≤)
open import Claude.DialogueTreeHeight.MDomSquareOrbit fe
 using (Fsq ; MDom-iter-sq)

\end{code}

The predicate: `φ b ≤ (b ⊕ c) ⊗ ω^ β`, carrying `β ≥ 1` and `β < ε₀` (for the
exponent arithmetic) and `ValidMult (ω^ β)` (for the multiplier, via `MDom`).

\begin{code}

ExpDom : (𝓑 → 𝓑) → 𝓤₀ ̇
ExpDom φ = Σ β ꞉ 𝓑 , (S Z ≤ β) × (β < ε₀) × ValidMult (ω^ β)
         × (Σ c ꞉ 𝓑 , (c < ε₀) × ((b : 𝓑) → φ b ≤ ((b ⊕ c) ⊗ ω^ β)))

private
 Mof : {φ : 𝓑 → 𝓑} → MDom φ → 𝓑
 Mof d = pr₁ d

 cof : {φ : 𝓑 → 𝓑} → MDom φ → 𝓑
 cof d = pr₁ (pr₂ (pr₂ d))

 bof : {φ : 𝓑 → 𝓑} (d : MDom φ) (b : 𝓑) → φ b ≤ ((b ⊕ cof d) ⊗ Mof d)
 bof d = pr₂ (pr₂ (pr₂ (pr₂ d)))

ExpDom→MDom : {φ : 𝓑 → 𝓑} → ExpDom φ → MDom φ
ExpDom→MDom (β , β+ , β<ε₀ , vωβ , c , c<ε₀ , bd) = ω^ β , vωβ , c , c<ε₀ , bd

\end{code}

Ground application: an `ExpDom` function sends a `< ε₀` argument to `< ε₀`.

\begin{code}

ExpDom-app : {φ : 𝓑 → 𝓑} → ExpDom φ → (a : 𝓑) → a < ε₀ → φ a < ε₀
ExpDom-app eφ = MDom-app (ExpDom→MDom eφ)

\end{code}

Composition: the exponent ADDS. `MDom-∘` squares/multiplies the opaque
multiplier `ω^ βψ ⊗ ω^ βφ`; `ω^⊗` rewrites it to `ω^ (βψ ⊕ βφ)`.

\begin{code}

ExpDom-∘ : {φ ψ : 𝓑 → 𝓑} → ExpDom φ → ExpDom ψ → ExpDom (λ b → φ (ψ b))
ExpDom-∘ {φ} {ψ}
  eφ@(βφ , βφ+ , βφ<ε₀ , vφ , cφ , cφ<ε₀ , bφ)
  eψ@(βψ , βψ+ , βψ<ε₀ , vψ , cψ , cψ<ε₀ , bψ) =
    (βψ ⊕ βφ) , β+ , β<ε₀ , vω , (cψ ⊕ cφ) , c<ε₀ , bound
 where
  mdc : MDom (λ b → φ (ψ b))
  mdc = MDom-∘ (ExpDom→MDom eφ) (ExpDom→MDom eψ)

  β+ : S Z ≤ (βψ ⊕ βφ)
  β+ = ≤-trans βφ+ (⊕-increasing-left βψ βφ)

  β<ε₀ : (βψ ⊕ βφ) < ε₀
  β<ε₀ = ⊕-<-ε₀ βψ βφ βψ<ε₀ βφ<ε₀

  c<ε₀ : (cψ ⊕ cφ) < ε₀
  c<ε₀ = ⊕-<-ε₀ cψ cφ cψ<ε₀ cφ<ε₀

  vω : ValidMult (ω^ (βψ ⊕ βφ))
  vω = transport ValidMult (ω^⊗ βψ βφ) (validMult-⊗ vψ vφ)

  bound : (b : 𝓑) → φ (ψ b) ≤ ((b ⊕ (cψ ⊕ cφ)) ⊗ ω^ (βψ ⊕ βφ))
  bound b = transport (λ z → φ (ψ b) ≤ ((b ⊕ (cψ ⊕ cφ)) ⊗ z))
                      (ω^⊗ βψ βφ) (bof mdc b)

\end{code}

The self-composition orbit: the exponent DOUBLING-ORBITS to `β ⊗ ω`. The `k`-th
self-composite (`MDom-iter-sq`) has multiplier `iter sq (ω^ β) k`, dominated by
`ω^ (β ⊗ ω)` via `sq-orbit-≤` (each `iter sq (ω^ β) k ≤ ω^ (β ⊗ ι[2ᵏ]) ≤
ω^ (β ⊗ ω)`); the constant orbit `iter double c` is `≤ L (iter double c) < ε₀`.

\begin{code}

ExpDom-sq-orbit : {φ : 𝓑 → 𝓑} → ExpDom φ
                → ExpDom (λ b → L (λ k → iter Fsq φ k b))
ExpDom-sq-orbit {φ} eφ@(β , β+ , β<ε₀ , vωβ , c , c<ε₀ , bd) =
    (β ⊗ ω) , βω+ , βω<ε₀ , vω∞ , c∞ , c∞<ε₀ , newbound
 where
  hφ : MDom φ
  hφ = ExpDom→MDom eφ

  βω+ : S Z ≤ (β ⊗ ω)
  βω+ = ≤-trans β+ (x-≤-x⊗ β ω ω-pos)

  βω<ε₀ : (β ⊗ ω) < ε₀
  βω<ε₀ = ⊗-<-ε₀ β ω β<ε₀ (tower-<-ε₀ 0)

  vω∞ : ValidMult (ω^ (β ⊗ ω))
  vω∞ = one-≤-ω^ (β ⊗ ω) , dbl-ω^ β β+ , ω^-<-ε₀ (β ⊗ ω) βω<ε₀

  c∞ : 𝓑
  c∞ = L (λ k → iter double c k)

  c∞<ε₀ : c∞ < ε₀
  c∞<ε₀ = double-orbit-<-ε₀ c c<ε₀

  Mk-eq : (k : ℕ) → Mof (MDom-iter-sq hφ k) ＝ iter sq (ω^ β) k
  Mk-eq zero     = refl
  Mk-eq (succ k) = ap (λ z → z ⊗ z) (Mk-eq k)

  ck-eq : (k : ℕ) → cof (MDom-iter-sq hφ k) ＝ iter double c k
  ck-eq zero     = refl
  ck-eq (succ k) = ap double (ck-eq k)

  Mk≤ : (k : ℕ) → Mof (MDom-iter-sq hφ k) ≤ ω^ (β ⊗ ω)
  Mk≤ k = transport (λ z → z ≤ ω^ (β ⊗ ω)) ((Mk-eq k) ⁻¹)
            (≤-trans (sq-orbit-≤ β (ω^ β) (≤-refl (ω^ β)) k)
                     (ω^-mono (⊗-mono-right β
                                (≤-L-upper-bound ι[_] (pow2 k)))))

  ck≤ : (k : ℕ) → cof (MDom-iter-sq hφ k) ≤ c∞
  ck≤ k = transport (λ z → z ≤ c∞) ((ck-eq k) ⁻¹)
            (≤-L-upper-bound (λ j → iter double c j) k)

  newbound : (b : 𝓑)
           → L (λ k → iter Fsq φ k b) ≤ ((b ⊕ c∞) ⊗ ω^ (β ⊗ ω))
  newbound b = ≤-L (λ k → ≤-trans (bof (MDom-iter-sq hφ k) b) (dom k))
   where
    dom : (k : ℕ)
        → ((b ⊕ cof (MDom-iter-sq hφ k)) ⊗ Mof (MDom-iter-sq hφ k))
        ≤ ((b ⊕ c∞) ⊗ ω^ (β ⊗ ω))
    dom k = ≤-trans (⊗-mono-left (⊕-mono-right b (ck≤ k))
                                 (Mof (MDom-iter-sq hφ k)))
                    (⊗-mono-right (b ⊕ c∞) (Mk≤ k))

\end{code}
