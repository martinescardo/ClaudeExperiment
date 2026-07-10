Heights of dialogue trees, constructively.

This is the constructive counterpart of
`Claude.DialogueTreeHeight.Classical`. There the height
of a dialogue tree was interpreted as a genuine ordinal in
`Ordinal 𝓤₀`, and the grafting and generic lemmas needed excluded middle,
because the successor map on ordinals is not monotone without it (see
`succ-not-necessarily-monotone` in `Ordinals.AdditionProperties`).

Here we instead take the height to be a *Brouwer ordinal code*
(`Ordinals.BrouwerCodes`), and we equip the codes with their syntactic
order, for which the successor is monotone *by construction*. The order and
addition on the codes are pure ordinal arithmetic, now factored out into
`Claude.BrouwerOrdinals.Order` (re-exported below); this module adds the height
function and its lemmas (§§1–2 of
`EffectfulForcing/DialogueTreeHeight/dialogue-tree-height-epsilon0.md`). The
only assumption is function extensionality, used solely for Lemma 1.

The height of a dialogue tree `d : B ℕ` is the Brouwer code

    height (η n)   = Z
    height (β φ i) = L (λ n → S (height (φ n))),

i.e. `0` at a leaf and `sup_n (height (φ n) + 1)` at a query node. Under
the standard interpretation `⟦_⟧₀ : B → Ordinal 𝓤₀` of
`Ordinals.BrouwerCodesInterpretations`, this code denotes precisely the
rank of the underlying ℕ-branching tree.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.Constructive
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import Claude.BrouwerOrdinals.Order fe public

\end{code}

The height of a dialogue tree, as a Brouwer ordinal code.

\begin{code}

height : B ℕ → 𝓑
height (η n)   = Z
height (β φ i) = L (λ n → S (height (φ n)))

\end{code}

Lemma 1. Relabelling the leaves (the action of the dialogue functor
`B-functor f = kleisli-extension (η ∘ f)`) does not change the height,
since the height ignores leaf values and depends only on the branching
structure. This is the only result that uses function extensionality.

\begin{code}

height-relabel : (f : ℕ → ℕ) (d : B ℕ)
               → height (B-functor f d) ＝ height d
height-relabel f (η n)   = refl
height-relabel f (β φ i) =
 ap L (dfunext fe (λ j → ap S (height-relabel f (φ j))))

height-B-functor-succ : (d : B ℕ) → height (B-functor succ d) ＝ height d
height-B-functor-succ = height-relabel succ

\end{code}

Lemma 3 (grafting). If every tree `g k` grafted at the leaves has height
at most `b`, then grafting them onto `d` via the Kleisli extension yields
a tree of height at most `b ⊕ height d`. The summand `b` is on the left:
the structure of `d` sits above the grafted trees. The successor step
needs no side condition, so no classical assumption is required.

\begin{code}

height-kleisli-extension
 : (g : ℕ → B ℕ) (b : 𝓑)
 → ((k : ℕ) → height (g k) ≤ b)
 → (d : B ℕ)
 → height (kleisli-extension g d) ≤ (b ⊕ height d)
height-kleisli-extension g b ϕ (η k)   = ϕ k
height-kleisli-extension g b ϕ (β φ i) =
 ≤-L-mono (λ j → ≤-S (height-kleisli-extension g b ϕ (φ j)))

\end{code}

Lemma 2 (the generic point). Applying the generic point adds at most one
to the height.

\begin{code}

height-generic : (d : B ℕ) → height (generic d) ≤ S (height d)
height-generic (η n)   = ≤-L (λ j → ≤-S ≤-Z)
height-generic (β φ i) =
 ≤-L (λ j → ≤-S (≤-trans
                  (height-generic (φ j))
                  (≤-ℓ j (≤-refl (S (height (φ j)))))))

\end{code}
