PROTOTYPE (not in the tour, not depended on): the **self-composition orbit** for
the multiplier-dominated class `MDom`.

Design note: `dialogue-tree-height-decoupling.md`. `MultDominated.MDom-orbit`
closes the *ground* recursor — iterating a body `φ : 𝓑 → 𝓑` on a starting
*value*, raise `M ↦ ω^(M ⊗ ω)`. The System T term the affine route could not
reach is the *higher-type* recursor `Iter g₀ (λ g → g ∘ g)`, whose numeral
majorant is the pointwise sup of the **self-composites** `g₀ , g₀∘g₀ ,
g₀∘g₀∘g₀∘g₀ , …` — `g₀` composed `2ᵏ` times. Its per-step multiplier is not the
fixed `ω`-raise but a genuine **squaring**: `MultDominated.MDom-∘` already proves
that `φ ∘ φ` squares the multiplier (`M ↦ M ⊗ M`) and doubles the constant
(`c ↦ c ⊕ c`), via the `crux` absorption. So the `k`-th self-composite has data

  `Mₖ = iter sq M`   (squaring orbit) ,  `cₖ = iter double c`  (doubling orbit),

and both orbits are already known `< ε₀`: `MultSquareOrbit.sq-orbit-≤` bounds
`iter sq M k ≤ ω^(b ⊗ ι[2ᵏ]) ≤ ω^(b ⊗ ω)` (the squaring exponent stays *inside*
one `ω`-power — the super-linear-but-`< ε₀` phenomenon), and
`Affine.double-orbit-≤` bounds `iter double c k ≤ c ⊗ ι[2ᵏ] ≤ c ⊗ ω`.

The payoff `MDom-sq-orbit`: the pointwise sup `λ b → L (λ k → (g₀ composed 2ᵏ
times) b)` is `MDom` again, at multiplier `ω^(b* ⊗ ω)` and constant
`L (iter double c)`. This is the first-order content of the open kernel — the
self-composition recursor closed for the multiplier-dominated shape, the multiplier
orbit supplied by `MultSquareOrbit` in the exact role `MultOrbit` plays for the
plain recursor. It reads the squaring factor off `MDom-∘`; it is not assumed.

Honest scope. This is the *ground* self-composition orbit (`φ : 𝓑 → 𝓑`). The
hereditary version — self-composing a *functional*, where each type level stacks
one further `ω^(–)` — and the fundamental theorem over it are the development this
underpins. The conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MDomSquareOrbit
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import Claude.BrouwerOrdinals.Order fe
 using (_≤_ ; _⊕_ ; ≤-Z ; ≤-S ; ≤-trans ; ≤-L ; ≤-L-upper-bound)
open import Claude.BrouwerOrdinals.Orbit fe using (ι[_] ; ω ; _⊗_)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ω^_ ; ω^-mono ; ω^-<-ε₀ ; one-≤-ω^ ;
        ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right ;
        S-<-ε₀ ; tower-<-ε₀)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (⊗-<-ε₀)
open import Claude.BrouwerOrdinals.Affine fe using (pow2 ; double ; double-orbit-<-ε₀)
open import Claude.BrouwerOrdinals.AffineClosure fe using (x-≤-x⊗)
open import Claude.BrouwerOrdinals.MultAffine fe using (ω-pos ; dbl-ω^)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; MDom ; MDom-∘ ; MDom-app)
open import Claude.BrouwerOrdinals.MultSquareOrbit fe
 using (sq ; sq-orbit-≤ ; w-≤-ω^ ; ≤-S-self)

\end{code}

Projections of an `MDom` witness.

\begin{code}

private
 Mof : {φ : 𝓑 → 𝓑} → MDom φ → 𝓑
 Mof d = pr₁ d

 cof : {φ : 𝓑 → 𝓑} → MDom φ → 𝓑
 cof d = pr₁ (pr₂ (pr₂ d))

 bof : {φ : 𝓑 → 𝓑} (d : MDom φ) (b : 𝓑) → φ b ≤ ((b ⊕ cof d) ⊗ Mof d)
 bof d = pr₂ (pr₂ (pr₂ (pr₂ d)))

\end{code}

Self-composition, and the `MDom` data of its `k`-th iterate — squaring the
multiplier and doubling the constant at each step, by `MDom-∘`.

\begin{code}

Fsq : (𝓑 → 𝓑) → (𝓑 → 𝓑)
Fsq g b = g (g b)

MDom-iter-sq : {φ : 𝓑 → 𝓑} → MDom φ → (k : ℕ) → MDom (iter Fsq φ k)
MDom-iter-sq hφ zero     = hφ
MDom-iter-sq hφ (succ k) = MDom-∘ (MDom-iter-sq hφ k) (MDom-iter-sq hφ k)

\end{code}

The multiplier of the `k`-th self-composite is exactly `iter sq M k`, and the
constant is exactly `iter double c k` — read off the `MDom-∘` recurrences
(`Mψ ⊗ Mφ`, `cψ ⊕ cφ`) at `ψ = φ`.

\begin{code}

Mk-eq : {φ : 𝓑 → 𝓑} (hφ : MDom φ) (k : ℕ)
      → Mof (MDom-iter-sq hφ k) ＝ iter sq (Mof hφ) k
Mk-eq hφ zero     = refl
Mk-eq hφ (succ k) = ap (λ z → z ⊗ z) (Mk-eq hφ k)

ck-eq : {φ : 𝓑 → 𝓑} (hφ : MDom φ) (k : ℕ)
      → cof (MDom-iter-sq hφ k) ＝ iter double (cof hφ) k
ck-eq hφ zero     = refl
ck-eq hφ (succ k) = ap double (ck-eq hφ k)

\end{code}

The self-composition orbit is `MDom`. The multiplier orbit `iter sq M`
dominates into `ω^(b* ⊗ ω)` by `sq-orbit-≤` (with `b* = S b`, `M ≤ ω^ b`); the
constant orbit `iter double c` dominates into `L (iter double c)` by
`≤-L-upper-bound`, which is `< ε₀` by `double-orbit-<-ε₀`.

\begin{code}

MDom-sq-orbit : {φ : 𝓑 → 𝓑} → MDom φ
              → MDom (λ b → L (λ k → iter Fsq φ k b))
MDom-sq-orbit {φ} hφ =
   M∞ , vM∞ , c∞ , c∞<ε₀ , newbound
 where
  Mφ : 𝓑
  Mφ = Mof hφ

  cφ : 𝓑
  cφ = cof hφ

  cφ<ε₀ : cφ < ε₀
  cφ<ε₀ = pr₁ (pr₂ (pr₂ (pr₂ hφ)))

  Mφ<ε₀ : Mφ < ε₀
  Mφ<ε₀ = pr₂ (pr₂ (pr₁ (pr₂ hφ)))

  bM : 𝓑
  bM = pr₁ (w-≤-ω^ Mφ Mφ<ε₀)

  bM<ε₀ : bM < ε₀
  bM<ε₀ = pr₁ (pr₂ (w-≤-ω^ Mφ Mφ<ε₀))

  Mφ≤ωbM : Mφ ≤ ω^ bM
  Mφ≤ωbM = pr₂ (pr₂ (w-≤-ω^ Mφ Mφ<ε₀))

  b* : 𝓑
  b* = S bM

  Mφ≤ωb* : Mφ ≤ ω^ b*
  Mφ≤ωb* = ≤-trans Mφ≤ωbM (ω^-mono (≤-S-self bM))

  M∞ : 𝓑
  M∞ = ω^ (b* ⊗ ω)

  vM∞ : ValidMult M∞
  vM∞ = one-≤-ω^ (b* ⊗ ω)
      , dbl-ω^ b* (≤-S ≤-Z)
      , ω^-<-ε₀ (b* ⊗ ω) (⊗-<-ε₀ b* ω (S-<-ε₀ bM bM<ε₀) (tower-<-ε₀ 0))

  c∞ : 𝓑
  c∞ = L (λ k → iter double cφ k)

  c∞<ε₀ : c∞ < ε₀
  c∞<ε₀ = double-orbit-<-ε₀ cφ cφ<ε₀

  Mk≤ : (k : ℕ) → Mof (MDom-iter-sq hφ k) ≤ M∞
  Mk≤ k = transport (λ z → z ≤ M∞) ((Mk-eq hφ k) ⁻¹)
            (≤-trans (sq-orbit-≤ b* Mφ Mφ≤ωb* k)
                     (ω^-mono (⊗-mono-right b*
                                (≤-L-upper-bound ι[_] (pow2 k)))))

  ck≤ : (k : ℕ) → cof (MDom-iter-sq hφ k) ≤ c∞
  ck≤ k = transport (λ z → z ≤ c∞) ((ck-eq hφ k) ⁻¹)
            (≤-L-upper-bound (λ j → iter double cφ j) k)

  newbound : (b : 𝓑) → L (λ k → iter Fsq φ k b) ≤ ((b ⊕ c∞) ⊗ M∞)
  newbound b = ≤-L (λ k → ≤-trans (bof (MDom-iter-sq hφ k) b) (dom k))
   where
    dom : (k : ℕ)
        → ((b ⊕ cof (MDom-iter-sq hφ k)) ⊗ Mof (MDom-iter-sq hφ k))
        ≤ ((b ⊕ c∞) ⊗ M∞)
    dom k = ≤-trans (⊗-mono-left (⊕-mono-right b (ck≤ k))
                                 (Mof (MDom-iter-sq hφ k)))
                    (⊗-mono-right (b ⊕ c∞) (Mk≤ k))

\end{code}

Consequently the self-composition recursor's orbit stays `< ε₀` from a `< ε₀`
start — the higher-type-recursor kernel closed, at ground, for the
multiplier-dominated shape.

\begin{code}

MDom-sq-orbit-<-ε₀ : {φ : 𝓑 → 𝓑} → MDom φ
                   → (b : 𝓑) → b < ε₀ → L (λ k → iter Fsq φ k b) < ε₀
MDom-sq-orbit-<-ε₀ hφ b b<ε₀ = MDom-app (MDom-sq-orbit hφ) b b<ε₀

\end{code}
