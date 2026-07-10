PROTOTYPE (not in the tour, not depended on): the bridge between the two layers
— the majorant-bounding predicate `MultHereditaryF.Good` and the affine-transformer
predicate `AffTransformerPredicate.JAff′` — and the base cases of the fundamental
theorem in the combined predicate `GoodJ`.

Design note: `dialogue-tree-height-decoupling.md`. `Good σ φ = Σ T , GoodT σ T ×
(∀ w , Bnd σ w T φ)` bounds a *majorant* `φ : Maj σ` by a transformer `T : 𝕋 σ`;
`JAff′ σ T` is exactly the affine structure of that same `T` that forces the
ground bound `< ε₀` even at higher type. The combined predicate carries both:

  `GoodJ σ φ = Σ T , GoodT σ T × JAff′ σ T × (∀ w , Bnd σ w T φ)`.

Ground extraction `GoodJ-ι-to-<ε₀` reads the `< ε₀` bound off `JAff′`'s data
(`(D Z ⊕ c) ⊗ M < ε₀`), sharpening `Good-ι-to-<ε₀` (which only knew the abstract
`T Z < ε₀`). The base combinators compose directly: their transformers
(`Good-Zero/Succ/Ω`) are exactly the shapes `JAff′-ι-id`/`JAff′-id`/`JAff′-Succ`
prove — so `GoodJ-Zero/Succ/Ω` are the existing `Good-*` witnesses with the
matching `JAff′` slotted in. This is the composition test: the two independently
built layers meet with no adapter.

Honest scope: the recursor/`K`/`S` steps of the `GoodJ` induction (and a
higher-order `μ-Iter`) are the remaining work — `IterFnProto`/`AffCombinators`
supply the `JAff′` half of each; the `Bnd` half is the existing `Good-*`
machinery. The conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.AffFundamental
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.BrouwerOrdinals.Order fe using (_≤_ ; _⊕_ ; ≤-trans ; ≤-S ; ≤-Z)
open import Claude.BrouwerOrdinals.Orbit fe using (ω ; _⊗_)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ⊕-<-ε₀ ; S-<-ε₀)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (⊗-<-ε₀)
open import Claude.BrouwerOrdinals.AffineClosure fe using (Z<ε₀)
open import Claude.DialogueTreeHeight.Majorant fe using (Maj)
open import Claude.DialogueTreeHeight.MultHereditaryF fe
 using (𝕋 ; GoodT ; Bnd ; Good)
open import Claude.DialogueTreeHeight.AffTransformerPredicate fe
 using (JAff′)
open import Claude.DialogueTreeHeight.AffCombinators fe
 using (goodId ; JAff′-ι-id ; JAff′-id ; JAff′-Succ ;
        JAff′-app-ι ; JAff′-app-fn)

\end{code}

The combined predicate: a majorant is `GoodJ` when its bounding transformer is
also `JAff′`.

\begin{code}

GoodJ : (σ : type) → Maj σ → 𝓤₀ ̇
GoodJ σ φ = Σ T ꞉ 𝕋 σ , GoodT σ T × JAff′ σ T × ((w : 𝓑) → Bnd σ w T φ)

\end{code}

Ground extraction: `GoodJ ι a` gives `a < ε₀`, read off `JAff′`'s data.

\begin{code}

GoodJ-ι-to-<ε₀ : (a : 𝓑) → GoodJ ι a → a < ε₀
GoodJ-ι-to-<ε₀ a (T , gT , (D , c , M , gD , cε , (_ , _ , M<ε₀) , b) , bnd) =
 ≤-trans (≤-S (≤-trans (bnd Z) (b Z)))
         (⊗-<-ε₀ (D Z ⊕ c) M
                 (⊕-<-ε₀ (D Z) c (pr₁ gD Z Z<ε₀) cε) M<ε₀)

\end{code}

The base combinators: existing `Good-*` transformer + the matching `JAff′`.

\begin{code}

GoodJ-Zero : GoodJ ι Z
GoodJ-Zero = (λ w → w) , goodId , JAff′-ι-id , (λ w → ≤-Z)

GoodJ-Succ : GoodJ (ι ⇒ ι) (λ a → a)
GoodJ-Succ = (λ Tg → Tg) , (λ Tg gTg → gTg) , JAff′-id
           , (λ w g Tg gTg gg → gg w)

GoodJ-Ω : GoodJ (ι ⇒ ι) (λ a → S a)
GoodJ-Ω = (λ Tg w → S (Tg w))
        , (λ Tg (gp , gm) → (λ w w<ε₀ → S-<-ε₀ (Tg w) (gp w w<ε₀))
                          , (λ w w′ w≤w′ → ≤-S (gm w w′ w≤w′)))
        , JAff′-Succ
        , (λ w g Tg gTg gg → ≤-S (gg w))

\end{code}

The application induction step composes at every type: the `Bnd` half is
`MultHereditaryF.Good-app`'s result transformer `TF TG`, the `JAff′` half is
`AffCombinators.JAff′-app-{ι,fn}` on that same `TF TG`. Split on the argument's
type (ground absorbed by value; function fed through the transformer clause).

\begin{code}

GoodJ-app : (σ τ : type) (F : Maj (σ ⇒ τ)) (G : Maj σ)
          → GoodJ (σ ⇒ τ) F → GoodJ σ G → GoodJ τ (F G)
GoodJ-app ι τ F G (TF , gTF , jTF , bF) (TG , gTG , jTG , bG) =
   TF TG , gTF TG gTG , JAff′-app-ι τ TF TG gTG jTF
 , (λ w → bF w G TG gTG bG)
GoodJ-app (σ₁ ⇒ σ₂) τ F G (TF , gTF , jTF , bF) (TG , gTG , jTG , bG) =
   TF TG , gTF TG gTG , JAff′-app-fn σ₁ σ₂ τ TF TG jTF jTG
 , (λ w → bF w G TG gTG bG)

\end{code}
