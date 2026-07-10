Design H, stage 2d(i): the good-inputs orbit — the recursor's `GoodT` side
over the tower.

`MultHereditaryFAff.orbit-good-aff` consumes an inner-affine bound at *all*
transformers. The tower's bound relation (`BndH` plus `selfD`) delivers the
affine domination only at *good* transformers — which suffices: the orbit
engine only ever applies the bound to the iterates `iter Tg Ta k`, and
these are good by `GoodT-iter` when `Tg` maps good to good. This module is
the mirror of `orbit-good-aff` with the goodness threaded: from a `GoodT`
functional `Tg` that is inner-affine *on good inputs*, the orbit
`Torbit Tg Ta` of a good start is good. Also here: `BndH-to-aff-good`,
extracting the good-inputs affine bound from a tower argument's pack via
`pack-to-Tracked`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryHM5
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ω^_ ; ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right ;
        ⊕-increasing-right ; ⊕-<-ε₀ ; ω^-<-ε₀ ; tower-<-ε₀)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊗-assoc ; ⊕-increasing-left)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (⊗-<-ε₀)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (x-≤-x⊗)
open import Claude.BrouwerOrdinals.MultAffine fe
 using (mbody-orbit-≤)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; ω-valid ; validMult-⊗)
open import Claude.DialogueTreeHeight.MultHereditaryF fe
 using (𝕋 ; GoodT ; Torbit ; GoodT-iter)
open import Claude.DialogueTreeHeight.MultHereditaryFAff fe
 using (⊕-dup-≤-⊗ω)
open import Claude.DialogueTreeHeight.MultHereditaryG fe
 using (GFun ; Tracked)
open import Claude.BrouwerOrdinals.MultBump fe
 using (bumpk ; bumpk-valid ; bumpk-<-ε₀)
open import Claude.DialogueTreeHeight.MultHereditaryH fe
 using (_+ℕ_)
open import Claude.DialogueTreeHeight.MultHereditaryHM fe
 using (𝕂 ; ZPack)
open import Claude.DialogueTreeHeight.MultHereditaryHM4 fe
 using (BndH ; pack-to-Tracked ; ⊕-Z-left)

\end{code}

The orbit bound and goodness, from an affine domination on good inputs.
The proof is `MultHereditaryFAff.aff-orbit-≤`/`orbit-good-aff` with
`GoodT-iter` supplying the goodness at each application of the bound.

\begin{code}

orbit-goodT : (Tg : 𝕋 (ι ⇒ ι)) → GoodT (ι ⇒ ι) Tg
            → (D : 𝓑 → 𝓑) (c M : 𝓑)
            → GoodT ι D → (c < ε₀) → ValidMult M → (M < ε₀)
            → ((T : 𝕋 ι) → GoodT ι T
                → (w : 𝓑) → Tg T w ≤ ((D w ⊕ (T w ⊕ c)) ⊗ M))
            → (Ta : 𝕋 ι) → GoodT ι Ta → GoodT ι (Torbit Tg Ta)
orbit-goodT Tg gTg D c M (Dpres , Dmono) c<ε₀ vM M<ε₀ aff
            Ta gTa@(Tapres , Tamono) = pres , mono
 where
  vM′ : ValidMult (ω ⊗ M)
  vM′ = validMult-⊗ ω-valid vM

  M′+ : S Z ≤ (ω ⊗ M)
  M′+ = pr₁ vM′

  M′dbl : (ι[ 2 ] ⊗ (ω ⊗ M)) ≤ (ω ⊗ M)
  M′dbl = pr₁ (pr₂ vM′)

  orbit-≤ : (w : 𝓑) → Torbit Tg Ta w
                       ≤ (((D w ⊕ Ta w) ⊕ c) ⊗ ω^ ((ω ⊗ M) ⊗ ω))
  orbit-≤ w =
   ≤-trans (≤-L-mono (λ k → pr₁ (dom k)))
           (mbody-orbit-≤ (ω ⊗ M) M′+ M′dbl c (D w ⊕ Ta w))
   where
    mbody′ : 𝓑 → 𝓑
    mbody′ b = (b ⊕ c) ⊗ (ω ⊗ M)

    y : ℕ → 𝓑
    y k = iter mbody′ (D w ⊕ Ta w) k

    dom : (k : ℕ) → (iter Tg Ta k w ≤ y k) × (D w ≤ y k)
    dom zero     = ⊕-increasing-left (D w) (Ta w)
                 , ⊕-increasing-right (D w) (Ta w)
    dom (succ k) = step , Dstep
     where
      gk : GoodT ι (iter Tg Ta k)
      gk = GoodT-iter Tg Ta gTg gTa k

      ih₁ : iter Tg Ta k w ≤ y k
      ih₁ = pr₁ (dom k)

      ih₂ : D w ≤ y k
      ih₂ = pr₂ (dom k)

      zone≤ : (D w ⊕ (iter Tg Ta k w ⊕ c)) ≤ (y k ⊕ (y k ⊕ c))
      zone≤ = ≤-trans (⊕-mono-left ih₂ (iter Tg Ta k w ⊕ c))
                      (⊕-mono-right (y k) (⊕-mono-left ih₁ c))

      absorb : (y k ⊕ (y k ⊕ c)) ≤ ((y k ⊕ c) ⊗ ω)
      absorb = ≤-trans
                (⊕-mono-left (⊕-increasing-right (y k) c) (y k ⊕ c))
                (⊕-dup-≤-⊗ω (y k ⊕ c))

      step : iter Tg Ta (succ k) w ≤ y (succ k)
      step = transport (λ z → iter Tg Ta (succ k) w ≤ z)
                       (⊗-assoc (y k ⊕ c) ω M)
                       (≤-trans (aff (iter Tg Ta k) gk w)
                                (⊗-mono-left (≤-trans zone≤ absorb) M))

      Dstep : D w ≤ y (succ k)
      Dstep = ≤-trans ih₂
               (≤-trans (⊕-increasing-right (y k) c)
                        (x-≤-x⊗ (y k ⊕ c) (ω ⊗ M) M′+))

  pres : (w : 𝓑) → w < ε₀ → Torbit Tg Ta w < ε₀
  pres w w<ε₀ = ≤-trans (≤-S (orbit-≤ w)) bound<ε₀
   where
    bound<ε₀ : (((D w ⊕ Ta w) ⊕ c) ⊗ ω^ ((ω ⊗ M) ⊗ ω)) < ε₀
    bound<ε₀ =
     ⊗-<-ε₀ ((D w ⊕ Ta w) ⊕ c) (ω^ ((ω ⊗ M) ⊗ ω))
            (⊕-<-ε₀ (D w ⊕ Ta w) c
                    (⊕-<-ε₀ (D w) (Ta w) (Dpres w w<ε₀) (Tapres w w<ε₀))
                    c<ε₀)
            (ω^-<-ε₀ ((ω ⊗ M) ⊗ ω)
                     (⊗-<-ε₀ (ω ⊗ M) ω
                             (⊗-<-ε₀ ω M (tower-<-ε₀ 0) M<ε₀)
                             (tower-<-ε₀ 0)))

  mono : (w w′ : 𝓑) → w ≤ w′ → Torbit Tg Ta w ≤ Torbit Tg Ta w′
  mono w w′ w≤w′ =
   ≤-L-mono (λ k → pr₂ (GoodT-iter Tg Ta gTg gTa k) w w′ w≤w′)

\end{code}

Extracting the good-inputs affine bound from a tower argument: instantiate
the argument's `BndH` at the self-datum `(T , gT)` and dominate through the
tracked pack.

\begin{code}

BndH-to-aff-good : (Tg : 𝕋 (ι ⇒ ι)) (kg : 𝕂 (ι ⇒ ι))
                 → BndH (ι ⇒ ι) Tg kg
                 → Σ D ꞉ (𝓑 → 𝓑) , Σ c ꞉ 𝓑 , Σ M ꞉ 𝓑 ,
                      GoodT ι D × (c < ε₀) × ValidMult M × (M < ε₀)
                    × ((T : 𝕋 ι) → GoodT ι T
                        → (w : 𝓑) → Tg T w ≤ ((D w ⊕ (T w ⊕ c)) ⊗ M))
BndH-to-aff-good Tg (F , D , c , M , j , gD , cε , vM , Mε , za) bndg =
 D , c , bumpk (j +ℕ 0) (M ⊕ Z)
 , gD , cε , bumpk-valid (j +ℕ 0) vM , bumpk-<-ε₀ (j +ℕ 0) Mε
 , bound
 where
  bound : (T : 𝕋 ι) → GoodT ι T
        → (w : 𝓑)
        → Tg T w ≤ ((D w ⊕ (T w ⊕ c)) ⊗ bumpk (j +ℕ 0) (M ⊕ Z))
  bound T gT w =
   ≤-trans (bndg T (T , gT) (λ w′ → ≤-refl (T w′)) w)
           (transport
             (λ z → pr₁ (F (T , gT)) w
                     ≤ ((D w ⊕ (z ⊕ c)) ⊗ bumpk (j +ℕ 0) (M ⊕ Z)))
             (⊕-Z-left (T w))
             (za (T , gT) w))

\end{code}
