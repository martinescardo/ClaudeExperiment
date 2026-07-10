Heights of dialogue trees.

This file formalises §§1–2 of the companion note
`EffectfulForcing/DialogueTreeHeight/dialogue-tree-height-epsilon0.md`: the height of a
dialogue tree as a genuine ordinal, and the height calculus for the
basic operations out of which the dialogue-tree semantics `B⟦_⟧` of
System T is built (relabelling, the generic point, and grafting along
the dialogue monad's Kleisli extension).

The height of a dialogue tree `d : B ℕ` is the ordinal

    h (η n)   = 𝟘ₒ
    h (β φ i) = sup_n (h (φ n) +ₒ 𝟙ₒ),

i.e. the rank of the ℕ-branching well-founded tree underlying `d`.

We interpret heights into the ordinal `Ordinal 𝓤₀` (the "standard
interpretation" of Brouwer ordinal codes, cf.
`Ordinals.BrouwerCodesInterpretations`). At that scale the successor map
on ordinals is not monotone without excluded middle (see
`succ-not-necessarily-monotone` and `succ-monotone` in
`Ordinals.AdditionProperties`), so the grafting and generic lemmas,
which add `𝟙ₒ` on top of a `⊴`-inequality, are proved classically: the
module assumes `EM 𝓤₁`. This is harmless for the intended application,
which is the classical proof-theoretic bound `< ε₀`.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.Univalence
open import UF.PropTrunc
open import UF.Size
open import UF.ClassicalLogic

module Claude.DialogueTreeHeight.Classical
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
        (em : EM 𝓤₁)
       where

open import UF.FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import EffectfulForcing.MFPSAndVariations.Dialogue
open import Ordinals.Arithmetic fe
open import Ordinals.AdditionProperties ua
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Type

open suprema pt sr
open PropositionalTruncation pt

\end{code}

The height of a dialogue tree, as an ordinal.

\begin{code}

height : B ℕ → Ordinal 𝓤₀
height (η n)   = 𝟘ₒ
height (β φ i) = sup (λ n → height (φ n) +ₒ 𝟙ₒ)

\end{code}

Lemma 1. Relabelling the leaves of a dialogue tree (the action of the
dialogue functor `B-functor f = kleisli-extension (η ∘ f)`) does not
change its height, because the height ignores the values stored at
leaves and depends only on the branching structure.

\begin{code}

height-relabel : (f : ℕ → ℕ) (d : B ℕ)
               → height (B-functor f d) ＝ height d
height-relabel f (η n)   = refl
height-relabel f (β φ i) =
 ap sup (dfunext fe' (λ j → ap (_+ₒ 𝟙ₒ) (height-relabel f (φ j))))

\end{code}

In particular the successor of dialogue trees, `succ' = B-functor succ`
(as defined in `MFPS-XXIX.lagda`), preserves height.

\begin{code}

height-B-functor-succ : (d : B ℕ) → height (B-functor succ d) ＝ height d
height-B-functor-succ = height-relabel succ

\end{code}

Lemma 3 (grafting). If every tree `g k` grafted at the leaves has height
at most `b`, then grafting them onto `d` via the Kleisli extension gives
a tree of height at most `b +ₒ height d`. The summand `b` is on the
*left*: the structure of `d` sits above the grafted trees and is added
on top.

\begin{code}

height-kleisli-extension
 : (g : ℕ → B ℕ) (b : Ordinal 𝓤₀)
 → ((k : ℕ) → height (g k) ⊴ b)
 → (d : B ℕ)
 → height (kleisli-extension g d) ⊴ (b +ₒ height d)
height-kleisli-extension g b ϕ (η k) =
 transport (height (g k) ⊴_) ((𝟘ₒ-right-neutral b) ⁻¹) (ϕ k)
height-kleisli-extension g b ϕ (β φ i) =
 transport (height (kleisli-extension g (β φ i)) ⊴_) (e ⁻¹) s
 where
  e : (b +ₒ height (β φ i)) ＝ sup (λ j → b +ₒ (height (φ j) +ₒ 𝟙ₒ))
  e = +ₒ-preserves-inhabited-suprema pt sr b
       (λ j → height (φ j) +ₒ 𝟙ₒ) ∣ zero ∣

  comp : (j : ℕ)
       → (height (kleisli-extension g (φ j)) +ₒ 𝟙ₒ)
       ⊴ (b +ₒ (height (φ j) +ₒ 𝟙ₒ))
  comp j = ⊴-trans _ _ _
            (succ-monotone em
              (height (kleisli-extension g (φ j)))
              (b +ₒ height (φ j))
              (height-kleisli-extension g b ϕ (φ j)))
            (＝-to-⊴ _ _ (+ₒ-assoc b (height (φ j)) 𝟙ₒ))

  s : sup (λ j → height (kleisli-extension g (φ j)) +ₒ 𝟙ₒ)
    ⊴ sup (λ j → b +ₒ (height (φ j) +ₒ 𝟙ₒ))
  s = sup-monotone _ _ comp

\end{code}

Lemma 2 (the generic point). Applying the generic point adds at most one
to the height. The generic point is the Kleisli extension of `β η`, so
this is a direct induction (and could also be derived from the grafting
lemma).

\begin{code}

height-generic : (d : B ℕ) → height (generic d) ⊴ (height d +ₒ 𝟙ₒ)
height-generic (η n) =
 sup-is-lower-bound-of-upper-bounds
  (λ j → height (η j) +ₒ 𝟙ₒ)
  (height (η n) +ₒ 𝟙ₒ)
  (λ j → ⊴-refl _)
height-generic (β φ i) =
 ⊴-trans _ _ _
  (sup-monotone
    (λ j → height (generic (φ j)) +ₒ 𝟙ₒ)
    (λ j → (height (φ j) +ₒ 𝟙ₒ) +ₒ 𝟙ₒ)
    (λ j → succ-monotone em _ _ (height-generic (φ j))))
  (sup-is-lower-bound-of-upper-bounds
    (λ j → (height (φ j) +ₒ 𝟙ₒ) +ₒ 𝟙ₒ)
    (sup (λ j → height (φ j) +ₒ 𝟙ₒ) +ₒ 𝟙ₒ)
    (λ j → succ-monotone em _ _
            (sup-is-upper-bound (λ k → height (φ k) +ₒ 𝟙ₒ) j)))

\end{code}
