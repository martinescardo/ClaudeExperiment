PROTOTYPE (not in the tour, not depended on): the combinator cases of the
affine-transformer predicate `JAff′` — application, base leaves, and the
function-middle `S` diagonal at arbitrary result type.

Design note: `dialogue-tree-height-decoupling.md`. With the recursor closed at
every type level (`IterFnProto.JAff′-Iter-fn`) and the predicate/arithmetic
pinned (`AffTransformerPredicate`, `AffineTransformerProto`), these are the
remaining combinator steps of the fundamental theorem. Each is a
logical-relations step: it assumes the components are `JAff′` (and, for a ground
argument absorbed by value, that the argument is `GoodT`) and produces `JAff′`
of the composite.

* **Application** splits on the argument's type. A *ground* argument is absorbed
  into the accumulator `D` by its value (`JAff′-app-ι`, needing only `GoodT ι a`
  — the argument's own bound is not consumed). A *function* argument is fed to
  the transformer clause, its multiplier orbited into the result
  (`JAff′-app-fn` — the machine-checked `fnmid-S-affine` composition, exactly as
  in `JAff′-Iter-fn`'s step).
* **Base leaves** (`JAff′-id`, `JAff′-Succ`, `JAff′-add`, `JAff′-const`) are the
  all-ground shapes, where `BoundT′` agrees with `MultHereditaryFAffN.BoundT`
  definitionally — the witnesses port verbatim.
* **`JAff′-S-fnmid`** generalises `AffTransformerPredicate.JAff′-Sfnmid` from the
  result `ι` to an arbitrary result `τ`: the same identity feed of `γ Ta`'s data
  into `φ`'s transformer clause, now landing in `BoundT′ τ`.

Honest scope: `K` (projection at arbitrary type) and the *function-diagonal* `S`
are not here; with these plus the recursor and the μ-encoding, the fundamental
theorem `∀ t → JAff′ (μ t)` would assemble. The conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.AffCombinators
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.BrouwerOrdinals.Order fe using (_≤_ ; _⊕_ ; ≤-trans ; ≤-S ; ≤-Z)
open import Claude.BrouwerOrdinals.Orbit fe using (ι[_] ; ω ; _⊗_)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ⊕-<-ε₀ ; ⊕-increasing-right)
open import Claude.BrouwerOrdinals.Affine fe using (⊕-increasing-left)
open import Claude.BrouwerOrdinals.AffineClosure fe using (x-≤-x⊗ ; Z<ε₀ ; ι<ε₀)
open import Claude.BrouwerOrdinals.MultAffine fe using (ω-pos)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; ω-valid ; validMult-⊗)
open import Claude.DialogueTreeHeight.MultHereditaryF fe
 using (𝕋 ; GoodT ; GoodT-⊕)
open import Claude.DialogueTreeHeight.AffTransformerPredicate fe
 using (BoundT′ ; JAff′ ; BoundT′-mono-D)

\end{code}

Application. Ground argument (absorbed into `D` by value):

\begin{code}

JAff′-app-ι : (τ : type) (T : 𝕋 (ι ⇒ τ)) (a : 𝓑 → 𝓑)
            → GoodT ι a → JAff′ (ι ⇒ τ) T → JAff′ τ (T a)
JAff′-app-ι τ T a gA (D , c , M , gD , cε , vM , b) =
 (λ w → D w ⊕ a w) , c , M , GoodT-⊕ D a gD gA , cε , vM , b a

\end{code}

Function argument (fed to the transformer clause; multiplier orbited):

\begin{code}

JAff′-app-fn : (σ₁ σ₂ τ : type) (T : 𝕋 ((σ₁ ⇒ σ₂) ⇒ τ)) (a : 𝕋 (σ₁ ⇒ σ₂))
             → JAff′ ((σ₁ ⇒ σ₂) ⇒ τ) T → JAff′ (σ₁ ⇒ σ₂) a
             → JAff′ τ (T a)
JAff′-app-fn σ₁ σ₂ τ T a
  (D , c , M , gD , cε , vM , b)
  (Da , ca , Ma , gDa , caε , vMa , ba) =
    D , (ca ⊕ c) , ((Ma ⊗ ω) ⊗ M) , gD
  , ⊕-<-ε₀ ca c caε cε
  , validMult-⊗ (validMult-⊗ vMa ω-valid) vM
  , b a Da ca Ma caε vMa ba

\end{code}

Base leaves (all-ground; witnesses port verbatim from `MultHereditaryFAffN`).

\begin{code}

goodZ : GoodT ι (λ _ → Z)
goodZ = (λ w _ → Z<ε₀) , (λ w w′ _ → ≤-Z)

goodId : GoodT ι (λ w → w)
goodId = (λ w p → p) , (λ w w′ p → p)

JAff′-ι-id : JAff′ ι (λ w → w)
JAff′-ι-id = (λ w → w) , Z , ω , goodId , Z<ε₀ , ω-valid
 , (λ w → x-≤-x⊗ w ω ω-pos)

JAff′-id : JAff′ (ι ⇒ ι) (λ T → T)
JAff′-id = (λ _ → Z) , Z , ω , goodZ , Z<ε₀ , ω-valid
 , (λ T w → ≤-trans (⊕-increasing-left Z (T w)) (x-≤-x⊗ (Z ⊕ T w) ω ω-pos))

JAff′-Succ : JAff′ (ι ⇒ ι) (λ T w → S (T w))
JAff′-Succ = (λ _ → Z) , ι[ 1 ] , ω , goodZ , ι<ε₀ 1 , ω-valid
 , (λ T w → ≤-trans (≤-S (⊕-increasing-left Z (T w)))
                    (x-≤-x⊗ ((Z ⊕ T w) ⊕ ι[ 1 ]) ω ω-pos))

JAff′-const : (Ta : 𝕋 ι) → GoodT ι Ta → JAff′ (ι ⇒ ι) (λ Tb → Ta)
JAff′-const Ta gTa = Ta , Z , ω , gTa , Z<ε₀ , ω-valid
 , (λ Tb w → ≤-trans (⊕-increasing-right (Ta w) (Tb w))
                     (x-≤-x⊗ (Ta w ⊕ Tb w) ω ω-pos))

JAff′-add : (C : 𝕋 ι) → GoodT ι C → JAff′ (ι ⇒ ι) (λ Tν w → C w ⊕ Tν w)
JAff′-add C gC = C , Z , ω , gC , Z<ε₀ , ω-valid
 , (λ Tν w → x-≤-x⊗ (C w ⊕ Tν w) ω ω-pos)

\end{code}

The function-middle `S` diagonal at arbitrary result type — the identity feed of
`γ Ta`'s affine data into `φ`'s transformer clause, landing in `BoundT′ τ`.

\begin{code}

JAff′-S-fnmid : (σ₁ σ₂ τ : type)
                (φ : 𝕋 (ι ⇒ (σ₁ ⇒ σ₂) ⇒ τ)) (γ : 𝕋 (ι ⇒ (σ₁ ⇒ σ₂)))
              → JAff′ (ι ⇒ (σ₁ ⇒ σ₂) ⇒ τ) φ → JAff′ (ι ⇒ (σ₁ ⇒ σ₂)) γ
              → JAff′ (ι ⇒ τ) (λ Ta → φ Ta (γ Ta))
JAff′-S-fnmid σ₁ σ₂ τ φ γ
  (Dφ , cφ , Mφ , gDφ , cφε , vMφ , bφ)
  (Dγ , cγ , Mγ , gDγ , cγε , vMγ , bγ) =
    Dφ , (cγ ⊕ cφ) , ((Mγ ⊗ ω) ⊗ Mφ) , gDφ
  , ⊕-<-ε₀ cγ cφ cγε cφε
  , validMult-⊗ (validMult-⊗ vMγ ω-valid) vMφ
  , (λ Ta → bφ Ta (γ Ta) (λ w → Dγ w ⊕ Ta w) cγ Mγ cγε vMγ (bγ Ta))

\end{code}

Dead-argument insertion (a ground argument the term ignores) and the ground `K`
projection. `JAff′-insert-ι` prepends a dead ground argument — the argument
accumulates into `D` but the bound is re-based back down by `BoundT′-mono-D`;
`JAff′-K` is the twofold projection `λ Ta Tb → Ta` at ground, ported verbatim.

\begin{code}

JAff′-insert-ι : (σ : type) (Ta : 𝕋 σ) → JAff′ σ Ta → JAff′ (ι ⇒ σ) (λ Tb → Ta)
JAff′-insert-ι σ Ta (D , c , M , gD , cε , vM , b) =
 D , c , M , gD , cε , vM
 , (λ Tb → BoundT′-mono-D σ Ta D (λ w → D w ⊕ Tb w) c M
             (λ w → ⊕-increasing-right (D w) (Tb w)) b)

JAff′-K : JAff′ (ι ⇒ ι ⇒ ι) (λ Ta Tb → Ta)
JAff′-K = (λ _ → Z) , Z , ω , goodZ , Z<ε₀ , ω-valid
 , (λ Ta Tb w → ≤-trans (⊕-increasing-left Z (Ta w))
                 (≤-trans (⊕-increasing-right (Z ⊕ Ta w) (Tb w))
                          (x-≤-x⊗ ((Z ⊕ Ta w) ⊕ Tb w) ω ω-pos)))

\end{code}
