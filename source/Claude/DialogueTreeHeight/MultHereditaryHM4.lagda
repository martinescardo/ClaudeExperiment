Design H, merged/doubled-budget fork — stage 2c: the predicate layer, for
`MultHereditaryHM`.

`MultHereditaryH4` retargeted at `MultHereditaryHM`. Everything ports
verbatim: the predicate (`BndH`/`LT`/`BndL`/`GoodH`) is structural over
`𝕂`, and the base-combinator packs (`packSucc`, `packΩ`) and
`pack-to-Tracked` touch only the *ground* `ZApply` clause, which the fork
leaves unchanged (the doubled budget lives in the *arrow* clause). So the
`2×` fork agrees with the original tower on everything at ground argument
type; the divergence appears only when a function-typed argument is consumed
(the `S` diagonal). The conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryHM4
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe
 using (ι[_] ; ω ; _⊗_)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; S-<-ε₀ ; tower-<-ε₀)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊕-increasing-left)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (x-≤-x⊗ ; Z<ε₀ ; ι<ε₀)
open import Claude.BrouwerOrdinals.MultAffine fe using (ω-pos)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; ω-valid)
open import Claude.DialogueTreeHeight.Majorant fe
 using (Maj ; μ-Zero ; μ-Succ ; μ-Ω)
open import Claude.DialogueTreeHeight.MultHereditaryF fe
 using (𝕋 ; GoodT)
open import Claude.DialogueTreeHeight.MultHereditaryG fe
 using (GFun ; dΩ ; Tracked)
open import Claude.BrouwerOrdinals.MultBump fe
 using (bumpk ; bumpk-valid ; bumpk-<-ε₀)
open import Claude.DialogueTreeHeight.MultHereditaryH fe
 using (_+ℕ_)
open import Claude.DialogueTreeHeight.MultHereditaryHM fe
 using (𝕂 ; ZPack ; ZApply ; ZCont)

\end{code}

The predicate.

\begin{code}

BndH : (σ : type) → 𝕋 σ → 𝕂 σ → 𝓤₀ ̇
BndH ι       T k = (w : 𝓑) → T w ≤ pr₁ k w
BndH (σ ⇒ τ) T k = (g : 𝕋 σ) (kg : 𝕂 σ)
                 → BndH σ g kg → BndH τ (T g) (pr₁ k kg)

LT : (σ : type) → 𝕋 σ → 𝓤₀ ̇
LT ι       T = GoodT ι T
LT (σ ⇒ τ) T = ((Tg : 𝕋 σ) → LT σ Tg → LT τ (T Tg))
             × (Σ k ꞉ 𝕂 (σ ⇒ τ) , BndH (σ ⇒ τ) T k)

BndL : (σ : type) → 𝓑 → 𝕋 σ → Maj σ → 𝓤₀ ̇
BndL ι       w T a = a ≤ T w
BndL (σ ⇒ τ) w T φ = (g : Maj σ) (Tg : 𝕋 σ) → LT σ Tg
                   → ((w′ : 𝓑) → BndL σ w′ Tg g) → BndL τ w (T Tg) (φ g)

GoodH : (σ : type) → Maj σ → 𝓤₀ ̇
GoodH σ φ = Σ T ꞉ 𝕋 σ , LT σ T × ((w : 𝓑) → BndL σ w T φ)

GoodH-ι-to-<ε₀ : (a : 𝓑) → GoodH ι a → a < ε₀
GoodH-ι-to-<ε₀ a (T , (Tpres , Tmono) , bnd) =
 ≤-trans (≤-S (bnd Z)) (Tpres Z Z<ε₀)

\end{code}

The base combinators, with their zone packs (empty accumulators reduce, so
each pack bound is an increasing chain into `⊗ ω`), and application (which
consumes the maps component; the argument's own `LT` supplies everything).

\begin{code}

GoodH-Zero : GoodH ι μ-Zero
GoodH-Zero =
 (λ w → w) , ((λ w w<ε₀ → w<ε₀) , (λ w w′ w≤w′ → w≤w′)) , (λ w → ≤-Z)

GoodH-Succ : GoodH (ι ⇒ ι) μ-Succ
GoodH-Succ =
 (λ Tg → Tg)
 , ((λ Tg gTg → gTg) , (kSucc , bndSucc))
 , (λ w g Tg gTg gg → gg w)
 where
  packSucc : ZPack ι ι (λ b → b)
  packSucc =
   (λ _ → Z) , Z , ω , 0
   , ((λ w _ → Z<ε₀) , (λ w w′ _ → ≤-Z))
   , Z<ε₀ , ω-valid , tower-<-ε₀ 0
   , (λ b w → ≤-trans (⊕-increasing-left Z (pr₁ b w))
               (≤-trans (⊕-increasing-left Z (Z ⊕ pr₁ b w))
                        (x-≤-x⊗ (Z ⊕ (Z ⊕ pr₁ b w)) ω ω-pos)))

  kSucc : 𝕂 (ι ⇒ ι)
  kSucc = (λ b → b) , packSucc

  bndSucc : BndH (ι ⇒ ι) (λ Tg → Tg) kSucc
  bndSucc = λ g kg bg → bg

GoodH-Ω : GoodH (ι ⇒ ι) μ-Ω
GoodH-Ω =
 (λ Tg w → S (Tg w))
 , ((λ Tg (gp , gm) → (λ w w<ε₀ → S-<-ε₀ (Tg w) (gp w w<ε₀))
                    , (λ w w′ w≤w′ → ≤-S (gm w w′ w≤w′)))
   , (kΩ , bndΩ))
 , (λ w g Tg gTg gg → ≤-S (gg w))
 where
  packΩ : ZPack ι ι dΩ
  packΩ =
   (λ _ → Z) , ι[ 1 ] , ω , 0
   , ((λ w _ → Z<ε₀) , (λ w w′ _ → ≤-Z))
   , ι<ε₀ 1 , ω-valid , tower-<-ε₀ 0
   , (λ b w → ≤-trans (≤-S (⊕-increasing-left Z (pr₁ b w)))
               (≤-trans (⊕-increasing-left Z (S (Z ⊕ pr₁ b w)))
                        (x-≤-x⊗ (Z ⊕ S (Z ⊕ pr₁ b w)) ω ω-pos)))

  kΩ : 𝕂 (ι ⇒ ι)
  kΩ = dΩ , packΩ

  bndΩ : BndH (ι ⇒ ι) (λ Tg w → S (Tg w)) kΩ
  bndΩ = λ g kg bg w → ≤-S (bg w)

GoodH-app : (σ τ : type) (F : Maj (σ ⇒ τ)) (G : Maj σ)
          → GoodH (σ ⇒ τ) F → GoodH σ G → GoodH τ (F G)
GoodH-app σ τ F G (TF , (mF , _) , bF) (TG , lG , bG) =
 TF TG , mF TG lG , (λ w → bF w G TG lG bG)

\end{code}

The recursor bridge: an `ι ⇒ ι` zone pack is a `Tracked` witness. `Z` is a
left unit for `⊕`, which erases the empty-accumulator noise; the budget
folds into the multiplier, which remains a valid multiplier below `ε₀`.

\begin{code}

⊕-Z-left : (x : 𝓑) → (Z ⊕ x) ＝ x
⊕-Z-left Z     = refl
⊕-Z-left (S b) = ap S (⊕-Z-left b)
⊕-Z-left (L f) = ap L (dfunext fe (λ n → ⊕-Z-left (f n)))

pack-to-Tracked : (F : GFun → GFun) → ZPack ι ι F → Tracked F
pack-to-Tracked F (D , c , M , j , gD , cε , vM , Mε , za) =
 D , c , bumpk (j +ℕ 0) (M ⊕ Z)
 , gD , cε , bumpk-valid (j +ℕ 0) vM
 , (λ b w → transport
             (λ z → pr₁ (F b) w
                     ≤ ((D w ⊕ (z ⊕ c)) ⊗ bumpk (j +ℕ 0) (M ⊕ Z)))
             (⊕-Z-left (pr₁ b w))
             (za b w))

\end{code}
