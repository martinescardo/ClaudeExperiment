Design G, second storey, first consumption point: the data-level ground-`S`
diagonal — joint binary tracking of data maps, and the closure of `Tracked`
under the diagonal `λ b → F b (G b)`.

`MultHereditaryG` transferred the unary affine calculus to data maps
(`Tracked`, `Tracked-∘`, the orbit). The Howard-tower fundamental theorem
additionally needs the tracked class closed under the *ground diagonal*: for
a binary data map `F : 𝔻 ι → 𝔻 ι → 𝔻 ι` jointly tracked in both arguments
(`Tracked₂`, the `Aff₂` shape read on bound functions) and a tracked
`G : 𝔻 ι → 𝔻 ι`, the diagonal `λ b → F b (G b)` is tracked
(`Tracked-diag`). This is the storey-2 obligation consuming storey 1, and —
as with `Tracked-∘` — it is proved by pure reuse: the dominating
transformers are affinely bounded by construction, `AffBounded-Sg-diag`
(module `MultHereditaryFAff2`) closes their diagonal, and the data-level
bound rides along by monotonicity. Also here: `Tracked₂`'s currying
(`Tracked₂-apply`) and the binary projections, mirroring `Aff₂`'s algebra.

With `MultBump` (the multiplier storey accounting) and this module, the
arithmetic for the two-storey collapse of the Howard tower is in place;
what remains is the tower predicate itself (`Trk`, mutual with the
zone-bound over types) and the level-polymorphic fundamental theorem. The
conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryG2
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe
 using (ω ; _⊗_ ; ⊕-mono-left ; ⊕-assoc)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right ;
        ⊕-increasing-right)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊕-increasing-left)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (x-≤-x⊗ ; Z<ε₀)
open import Claude.BrouwerOrdinals.MultAffine fe using (ω-pos)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; ω-valid)
open import Claude.DialogueTreeHeight.MultHereditaryF fe
 using (𝕋 ; GoodT ; GoodT-⊕)
open import Claude.DialogueTreeHeight.MultHereditaryFAff fe
 using (AffBounded)
open import Claude.DialogueTreeHeight.MultHereditaryFAff2 fe
 using (Aff₂ ; AffBounded-Sg-diag)
open import Claude.DialogueTreeHeight.MultHereditaryG fe
 using (GFun ; 𝔻 ; Tracked ; Taff ; Taff-mono)

\end{code}

Joint binary tracking, its dominating binary transformer, and the fact that
the dominating transformer is `Aff₂` by construction.

\begin{code}

Tracked₂ : (𝔻 ι → 𝔻 ι → 𝔻 ι) → 𝓤₀ ̇
Tracked₂ F = Σ D ꞉ (𝓑 → 𝓑) , Σ c ꞉ 𝓑 , Σ M ꞉ 𝓑 ,
                GoodT ι D × (c < ε₀) × ValidMult M
              × ((b₁ b₂ : 𝔻 ι) (w : 𝓑)
                   → pr₁ (F b₁ b₂) w
                     ≤ ((D w ⊕ (pr₁ b₁ w ⊕ (pr₁ b₂ w ⊕ c))) ⊗ M))

Taff₂ : (𝓑 → 𝓑) → 𝓑 → 𝓑 → 𝕋 (ι ⇒ ι ⇒ ι)
Taff₂ D c M = λ T₁ T₂ w → ((D w ⊕ (T₁ w ⊕ (T₂ w ⊕ c))) ⊗ M)

Taff₂-mono₂ : (D : 𝓑 → 𝓑) (c M : 𝓑) (T₁ T₂ T₂′ : 𝓑 → 𝓑)
            → ((w : 𝓑) → T₂ w ≤ T₂′ w)
            → (w : 𝓑) → Taff₂ D c M T₁ T₂ w ≤ Taff₂ D c M T₁ T₂′ w
Taff₂-mono₂ D c M T₁ T₂ T₂′ h w =
 ⊗-mono-left (⊕-mono-right (D w)
               (⊕-mono-right (T₁ w) (⊕-mono-left (h w) c))) M

Taff₂-aff : (D : 𝓑 → 𝓑) (c M : 𝓑)
          → GoodT ι D → c < ε₀ → ValidMult M
          → Aff₂ (Taff₂ D c M)
Taff₂-aff D c M gD cε vM = D , c , M , gD , cε , vM , (λ T₁ T₂ w → ≤-refl _)

\end{code}

Currying and the projections — `Aff₂`'s algebra read on data maps. Fixing
the first argument of a jointly tracked binary map gives a tracked unary
map with the fixed argument's bound joined into the summand.

\begin{code}

Tracked₂-apply : (F : 𝔻 ι → 𝔻 ι → 𝔻 ι) → Tracked₂ F
               → (b₁ : 𝔻 ι) → Tracked (F b₁)
Tracked₂-apply F (D , c , M , gD , cε , vM , t₂) b₁ =
 (λ w → D w ⊕ pr₁ b₁ w) , c , M
 , GoodT-⊕ D (pr₁ b₁) gD (pr₂ b₁) , cε , vM
 , (λ b₂ w → transport (λ z → pr₁ (F b₁ b₂) w ≤ (z ⊗ M))
              ((⊕-assoc (D w) (pr₁ b₁ w) (pr₁ b₂ w ⊕ c)) ⁻¹)
              (t₂ b₁ b₂ w))

Tracked₂-K : Tracked₂ (λ b₁ b₂ → b₁)
Tracked₂-K = (λ _ → Z) , Z , ω
 , ((λ w _ → Z<ε₀) , (λ w w′ _ → ≤-Z)) , Z<ε₀ , ω-valid
 , (λ b₁ b₂ w →
     ≤-trans (⊕-increasing-right (pr₁ b₁ w) (pr₁ b₂ w))
      (≤-trans (⊕-increasing-left Z (pr₁ b₁ w ⊕ pr₁ b₂ w))
               (x-≤-x⊗ (Z ⊕ (pr₁ b₁ w ⊕ pr₁ b₂ w)) ω ω-pos)))

Tracked₂-insert : (F : 𝔻 ι → 𝔻 ι) → Tracked F → Tracked₂ (λ b₁ → F)
Tracked₂-insert F (D , c , M , gD , cε , vM , t) =
 D , c , M , gD , cε , vM
 , (λ b₁ b₂ w →
     ≤-trans (t b₂ w)
      (⊗-mono-left (⊕-mono-right (D w)
                     (⊕-increasing-left (pr₁ b₁ w) (pr₁ b₂ w ⊕ c))) M))

\end{code}

The payoff: the tracked ground diagonal, by reuse of `AffBounded-Sg-diag`
on the dominating transformers.

\begin{code}

Tracked-diag : (F : 𝔻 ι → 𝔻 ι → 𝔻 ι) (G : 𝔻 ι → 𝔻 ι)
             → Tracked₂ F → Tracked G
             → Tracked (λ b → F b (G b))
Tracked-diag F G (DF , cF , MF , gDF , cFε , vMF , tF)
               (DG , cG , MG , gDG , cGε , vMG , tG) =
 finish (AffBounded-Sg-diag (Taff₂ DF cF MF) (Taff DG cG MG)
          (Taff₂-aff DF cF MF gDF cFε vMF)
          (DG , cG , MG , gDG , cGε , vMG , (λ T w → ≤-refl _)))
 where
  finish : AffBounded (λ Ta → Taff₂ DF cF MF Ta (Taff DG cG MG Ta))
         → Tracked (λ b → F b (G b))
  finish (D★ , c★ , M★ , gD★ , c★ε , vM★ , b★) =
   D★ , c★ , M★ , gD★ , c★ε , vM★ , bound
   where
    bound : (b : 𝔻 ι) (w : 𝓑)
          → pr₁ (F b (G b)) w ≤ ((D★ w ⊕ (pr₁ b w ⊕ c★)) ⊗ M★)
    bound b w =
     ≤-trans (tF b (G b) w)
      (≤-trans (Taff₂-mono₂ DF cF MF (pr₁ b) (pr₁ (G b))
                 (Taff DG cG MG (pr₁ b)) (tG b) w)
               (b★ (pr₁ b) w))

\end{code}
