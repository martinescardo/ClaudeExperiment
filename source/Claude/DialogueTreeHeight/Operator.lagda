The height-transform operator and its algebra (constructive).

This formalises the "engine" of the query-nesting-depth analysis
(`EffectfulForcing/DialogueTreeHeight/dialogue-tree-height-query-depth.md`): the
value-sensitive height operator

    H v (η n)   = v n
    H v (β φ i) = sup_j (H v (φ j) + 1),

which records how a dialogue tree turns an ordinal valuation `v` of its
leaves into an ordinal. Ordinary height is the special case `v = λ_. 0`.

The key results, all proved here:

* `height-is-H`     : `height x ＝ H (λ _ → Z) x`;
* `H-kleisli-extension` (the *composition law*):
                      `H v (kleisli-extension g d) ＝ H (λ k → H v (g k)) d`;
* `height-iter'`    (the *recursor identity*):
                      `height (kleisli-extension (iter f x) n)
                       ＝ H (λ k → height (iter f x k)) n`;
* `H-η`, `H-generic`, `H-B-functor-succ` : the combinator operator algebra,
  in particular that a leaf reads its exact count, while `generic` (the
  oracle) collapses the valuation to a supremum — the unique source of
  suprema.

Heights are Brouwer ordinal codes, reusing the constructive development.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.Operator
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import Claude.DialogueTreeHeight.Constructive fe

\end{code}

The value-sensitive height operator.

\begin{code}

H : (ℕ → 𝓑) → B ℕ → 𝓑
H v (η n)   = v n
H v (β φ i) = L (λ j → S (H v (φ j)))

\end{code}

Ordinary height is `H` at the constant-zero valuation.

\begin{code}

height-is-H : (x : B ℕ) → height x ＝ H (λ _ → Z) x
height-is-H (η n)   = refl
height-is-H (β φ i) = ap L (dfunext fe (λ j → ap S (height-is-H (φ j))))

\end{code}

The composition law: substituting along the Kleisli extension corresponds
to substituting the operators `H v (g k)` for the leaf valuation. This is
the engine of the whole analysis.

\begin{code}

H-kleisli-extension : (g : ℕ → B ℕ) (v : ℕ → 𝓑) (d : B ℕ)
                    → H v (kleisli-extension g d) ＝ H (λ k → H v (g k)) d
H-kleisli-extension g v (η k)   = refl
H-kleisli-extension g v (β φ i) =
 ap L (dfunext fe (λ j → ap S (H-kleisli-extension g v (φ j))))

\end{code}

The recursor identity: the count tree `n` acts on the orbit of heights
`k ↦ height (iter f x k) = height (fᵏ x)` through its operator `H _ n`.
This is the exact statement the bound on iteration turns on (a leaf count
selects the exact iterate; a `generic` count takes the supremum).

\begin{code}

height-iter' : (f : B ℕ → B ℕ) (x : B ℕ) (n : B ℕ)
             → height (kleisli-extension (iter f x) n)
             ＝ H (λ k → height (iter f x k)) n
height-iter' f x n =
   height-is-H (kleisli-extension (iter f x) n)
 ∙ H-kleisli-extension (iter f x) (λ _ → Z) n
 ∙ ap (λ - → H - n)
      (dfunext fe (λ k → (height-is-H (iter f x k)) ⁻¹))

\end{code}

The combinator operator algebra.

A leaf reads its exact count:

\begin{code}

H-η : (v : ℕ → 𝓑) (m : ℕ) → H v (η m) ＝ v m
H-η v m = refl

\end{code}

The oracle collapses the valuation to a supremum, independently of the leaf
— `generic` is the unique source of suprema (`L`):

\begin{code}

H-generic : (v : ℕ → 𝓑) (d : B ℕ)
          → H v (generic d) ＝ H (λ _ → L (λ j → S (v j))) d
H-generic v d = H-kleisli-extension (β η) v d

\end{code}

Relabelling by `succ` (the dialogue successor) reindexes the valuation:

\begin{code}

H-B-functor-succ : (v : ℕ → 𝓑) (x : B ℕ)
                 → H v (B-functor succ x) ＝ H (λ k → v (succ k)) x
H-B-functor-succ v x = H-kleisli-extension (η ∘ succ) v x

\end{code}
