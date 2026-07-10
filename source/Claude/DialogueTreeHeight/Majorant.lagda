The height majorant and the first-order fundamental theorem (constructive).

This is sub-development (II) of `dialogue-tree-height-frontier.md`: the
structural **term induction** that bounds the dialogue-tree height of a
first-order System T term by an explicit ordinal majorant. It is the
formalisation of Part I/II of `dialogue-tree-height-epsilon0-ordinal-
analysis.md`, restricted to the first-order fragment, where — crucially — a
*height-only* hereditary majorant suffices (the magnitude component is
needed only for the higher-type overshoot of that note's Part IV; at first
order Part II's affine class is purely ordinal).

The setup is a height-indexed logical relation à la `MFPS-XXIX.main-lemma`,
but with `height(·) ≤ ·` in place of the correctness `decode`:

* `Maj ι = 𝓑` (a Brouwer height bound), `Maj (σ⇒τ) = Maj σ → Maj τ`;
* `R ι x a := height x ≤ a`, `R (σ⇒τ) F φ := ∀ x a, R x a → R (F x) (φ a)`.

Each combinator gets a majorant, and the fundamental theorem follows by a
clean induction. The only non-trivial case is the ground recursor, whose
majorant is the **orbit supremum** `μ-Iter φ a ν = (sup_k φᵏ a) ⊕ ν`; its
correctness rides entirely on the already-verified conditional bound
`height-iter-≤-orbit-bound`, the uniform orbit bound being `sup_k φᵏ a`
itself.

The first-order fragment is the inductive type `T₁` below (`Iter` only at
type `ι`; `K, S`, application at all types — exactly the terms all of whose
iterations are ground). The outcome `height ⟦t⟧ ≤ μ t` is an *explicit*
majorant; that `μ t < ε₀` (for first order) is the separate affine-class
analysis, not done here — but every ingredient of it (`ω^_`, the tower, the
absorption `ω^ω ⊗ ω < ε₀`, additive closure) is ready in
`DialogueTreeHeight.Epsilon0`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.Majorant
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter ; Ķ ; Ş)
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import EffectfulForcing.MFPSAndVariations.MFPS-XXIX
 using (B-Set⟦_⟧ ; zero' ; succ' ; iter' ; Kleisli-extension)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Conditional fe
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (⊕-mono-right)

\end{code}

The hereditary majorant and the majorization relation.

\begin{code}

Maj : type → 𝓤₀ ̇
Maj ι       = 𝓑
Maj (σ ⇒ τ) = Maj σ → Maj τ

R : (σ : type) → B-Set⟦ σ ⟧ → Maj σ → 𝓤₀ ̇
R ι       x a = height x ≤ a
R (σ ⇒ τ) F φ = (x : B-Set⟦ σ ⟧) (a : Maj σ) → R σ x a → R τ (F x) (φ a)

\end{code}

The combinator majorants. `Zero ↦ 0`; `Succ ↦ id` (relabelling is
height-free); `Ω ↦ (+1)` (the oracle adds one); `K, S` the usual
projection/substitution; and the recursor majorant `μ-Iter`, the orbit
supremum plus the count height.

\begin{code}

μ-Zero : 𝓑
μ-Zero = Z

μ-Succ : 𝓑 → 𝓑
μ-Succ a = a

μ-Ω : 𝓑 → 𝓑
μ-Ω a = S a

μ-K : {σ τ : type} → Maj σ → Maj τ → Maj σ
μ-K a b = a

μ-S : {ρ σ τ : type} → Maj (ρ ⇒ σ ⇒ τ) → Maj (ρ ⇒ σ) → Maj ρ → Maj τ
μ-S φ γ a = φ a (γ a)

μ-Iter : (𝓑 → 𝓑) → 𝓑 → 𝓑 → 𝓑
μ-Iter φ a ν = L (λ k → iter φ a k) ⊕ ν

\end{code}

The combinator majorant lemmas — each combinator is majorized.

\begin{code}

R-Zero : R ι zero' μ-Zero
R-Zero = ≤-Z

R-Succ : R (ι ⇒ ι) succ' μ-Succ
R-Succ d b hd = transport (_≤ b) ((height-B-functor-succ d) ⁻¹) hd

R-Ω : R (ι ⇒ ι) generic μ-Ω
R-Ω d b hd = ≤-trans (height-generic d) (≤-S hd)

R-K : {σ τ : type} → R (σ ⇒ τ ⇒ σ) Ķ μ-K
R-K x a rx y b ry = rx

R-S : {ρ σ τ : type} → R ((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ) Ş μ-S
R-S φ φ′ rφ γ γ′ rγ x a rx = rφ x a rx (γ x) (γ′ a) (rγ x a rx)

\end{code}

The ground recursor. From `R (ι⇒ι) f φ` the orbit of heights `height (fᵏ x)`
is bounded *termwise* by the majorant orbit `φᵏ a`, hence *uniformly* by its
supremum `L (λ k → φᵏ a)`; the conditional bound then closes the iteration.

\begin{code}

R-Iter : R ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι) iter' μ-Iter
R-Iter f φ rf x a rx n ν rn =
 ≤-trans
  (height-iter-≤-orbit-bound f x (L (λ k → iter φ a k)) uniform n)
  (⊕-mono-right (L (λ k → iter φ a k)) rn)
 where
  orbit : (k : ℕ) → height (iter f x k) ≤ iter φ a k
  orbit zero     = rx
  orbit (succ k) = rf (iter f x k) (iter φ a k) (orbit k)

  uniform : (k : ℕ) → height (iter f x k) ≤ L (λ k → iter φ a k)
  uniform k = ≤-trans (orbit k) (≤-L-upper-bound (λ k → iter φ a k) k)

\end{code}

The first-order combinatory syntax `T₁`: `Iter` only at `ι`, everything else
polymorphic. These are exactly the System T terms whose every iteration is
ground.

\begin{code}

data T₁ : type → 𝓤₀ ̇ where
 Ω₁    : T₁ (ι ⇒ ι)
 Zero₁ : T₁ ι
 Succ₁ : T₁ (ι ⇒ ι)
 Iter₁ : T₁ ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι)
 K₁    : {σ τ : type}   → T₁ (σ ⇒ τ ⇒ σ)
 S₁    : {ρ σ τ : type} → T₁ ((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ)
 _·₁_  : {σ τ : type}   → T₁ (σ ⇒ τ) → T₁ σ → T₁ τ

infixl 6 _·₁_

⟦_⟧₁ : {σ : type} → T₁ σ → B-Set⟦ σ ⟧
⟦ Ω₁ ⟧₁     = generic
⟦ Zero₁ ⟧₁  = zero'
⟦ Succ₁ ⟧₁  = succ'
⟦ Iter₁ ⟧₁  = iter'
⟦ K₁ ⟧₁     = Ķ
⟦ S₁ ⟧₁     = Ş
⟦ t ·₁ u ⟧₁ = ⟦ t ⟧₁ ⟦ u ⟧₁

μ : {σ : type} → T₁ σ → Maj σ
μ Ω₁        = μ-Ω
μ Zero₁     = μ-Zero
μ Succ₁     = μ-Succ
μ Iter₁     = μ-Iter
μ K₁        = μ-K
μ S₁        = μ-S
μ (t ·₁ u)  = μ t (μ u)

\end{code}

The fundamental theorem: every closed first-order term is majorized by its
compositional majorant.

\begin{code}

fundamental : {σ : type} (t : T₁ σ) → R σ ⟦ t ⟧₁ (μ t)
fundamental Ω₁        = R-Ω
fundamental Zero₁     = R-Zero
fundamental Succ₁     = R-Succ
fundamental Iter₁     = R-Iter
fundamental K₁        = R-K
fundamental S₁        = R-S
fundamental (t ·₁ u)  = fundamental t ⟦ u ⟧₁ (μ u) (fundamental u)

\end{code}

Consequences: an explicit ordinal majorant for the height of any closed
first-order ground term, and in particular for the dialogue tree
`⟦ t ·₁ Ω₁ ⟧₁ = ⟦t⟧₁ generic` of a first-order `t : (ι⇒ι)⇒ι`.

\begin{code}

height-≤-μ : (t : T₁ ι) → height ⟦ t ⟧₁ ≤ μ t
height-≤-μ t = fundamental t

dialogue-height-≤-μ : (t : T₁ ((ι ⇒ ι) ⇒ ι))
                    → height (⟦ t ⟧₁ generic) ≤ μ (t ·₁ Ω₁)
dialogue-height-≤-μ t = fundamental (t ·₁ Ω₁)

\end{code}
