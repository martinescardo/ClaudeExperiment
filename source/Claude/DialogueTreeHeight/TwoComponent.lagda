The two-component (height, magnitude) majorant — the Howard route.

Taking Howard's result `|System T| = ε₀` seriously: the dialogue height is
the *ordinal rank* of a System T term's adaptive interaction with the oracle,
and Howard's ordinal assignment dominates such ranks. The earlier worry that
"height ⊥ value, so Howard is inapplicable" conflated value with rank — see
the corrected note in `DialogueTreeHeight.Conditional`.

The correct majorant is therefore Howard's *hereditarily-majorizable
functionals carrying both components*: at ground, a ground tree is majorized
by a pair

  `(a , V)` :  an ordinal height bound `a` (Brouwer code), and a magnitude
              function `V : ℕ → ℕ` (`V b` bounds the values under oracles
              `≤ b`),

related by `R₂ ι x (a , V) := height x ≤ a × mag-≤ V x`, and hereditarily by
`R₂ (σ⇒τ) F φ := ∀ x p, R₂ σ x p → R₂ τ (F x) (φ p)`.

The point of the second component is the recursor. The conjecture's residual
is the orbit bound `sup_k height (fᵏ x) < ε₀`, and it splits as

  **(A)** the *magnitude* orbit grows at a rate `< ε₀` — this is classical
          Howard (value-size of `iter f x k`, one System T term in `k`),
          *citable*; and
  **(B)** the dialogue-native bridge: the *height* increment per orbit step
          is `≤ ω^magnitude`, so height rides on (A) via the Count Lemma.

This module sets up the pair majorant, proves the structural combinators
(`Zero, Succ, Ω, K, S`, application) in two-component form — the magnitude
rows are exactly the `mag-*` lemmas, `Ω`'s magnitude row being the oracle
reset — and isolates the recursor as **(A) + (B)**: its magnitude is the
machine-checked `mag-kleisli` (the count is `≤ V b`, Lemma R1), and its
height is the machine-checked conditional bound, *given* the orbit-height
bound (B). So the whole open problem is localized to (B), with (A) a Howard
citation and everything else proved.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.TwoComponent
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Continuity using (Baire)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter ; Ķ ; Ş)
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import EffectfulForcing.MFPSAndVariations.MFPS-XXIX
 using (B-Set⟦_⟧ ; zero' ; succ' ; iter' ; Kleisli-extension)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Conditional fe
open import Claude.DialogueTreeHeight.Magnitude fe

\end{code}

The two-component majorant and the majorization relation.

\begin{code}

Mag : 𝓤₀ ̇
Mag = ℕ → ℕ

Maj₂ : type → 𝓤₀ ̇
Maj₂ ι       = 𝓑 × Mag
Maj₂ (σ ⇒ τ) = Maj₂ σ → Maj₂ τ

R₂ : (σ : type) → B-Set⟦ σ ⟧ → Maj₂ σ → 𝓤₀ ̇
R₂ ι       x (a , V) = (height x ≤ a) × mag-≤ V x
R₂ (σ ⇒ τ) F φ       = (x : B-Set⟦ σ ⟧) (p : Maj₂ σ) → R₂ σ x p → R₂ τ (F x) (φ p)

\end{code}

The structural combinators. Each row pairs a height fact (from the height
calculus L1–L3) with a magnitude fact (from `Magnitude`).

\begin{code}

R₂-Zero : R₂ ι zero' (Z , (λ _ → 0))
R₂-Zero = ≤-Z , mag-η 0

R₂-Succ : R₂ (ι ⇒ ι) succ' (λ (a , V) → (a , λ b → succ (V b)))
R₂-Succ d (a , V) (hd , md) =
 transport (_≤ a) ((height-B-functor-succ d) ⁻¹) hd ,
 mag-succ' V d md

R₂-Ω : R₂ (ι ⇒ ι) generic (λ (a , V) → (S a , λ b → b))
R₂-Ω d (a , V) (hd , md) =
 ≤-trans (height-generic d) (≤-S hd) ,
 mag-generic d

R₂-K : {σ τ : type} → R₂ (σ ⇒ τ ⇒ σ) Ķ (λ p q → p)
R₂-K x p rx y q ry = rx

R₂-S : {ρ σ τ : type}
     → R₂ ((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ) Ş (λ φ γ p → φ p (γ p))
R₂-S φ φ′ rφ γ γ′ rγ x p rx = rφ x p rx (γ x) (γ′ p) (rγ x p rx)

\end{code}

The recursor, as **(A) + (B)**. The *magnitude* of the ground iteration is
discharged outright (`mag-kleisli` / Lemma R1: the count `dialogue n α` is
`≤ V b`). The *height* is discharged by the machine-checked conditional
bound `height-iter-≤-orbit-bound`, *given* the orbit-height bound `b` — which
is exactly residual (B). The orbit-magnitude inputs to `mag-kleisli` are the
Howard component (A).

\begin{code}

R₂-Iter-ground
 : (f : B ℕ → B ℕ) (x : B ℕ)
   (b : 𝓑) (V W : Mag) (n : B ℕ)
 -- (B) the orbit-height bound (the residual; for first order it is `< ε₀`):
 → ((k : ℕ) → height (iter f x k) ≤ b)
 -- (A) the orbit-magnitude data (Howard): each iterate's magnitude, monotone:
 → ((k : ℕ) → mag-≤ (λ c → W k) (iter f x k))
 → ((k k′ : ℕ) → k ≤ℕ k′ → (c : ℕ) → W k ≤ℕ W k′)
 → mag-≤ V n
 → R₂ ι (iter' f x n) ((b ⊕ height n) , (λ c → W (V c)))
R₂-Iter-ground f x b V W n hb hW W-mono hn =
   height-iter-≤-orbit-bound f x b hb n
 , mag-kleisli (iter f x) (λ k _ → W k) V n hW W-mono hn

\end{code}

Application preserves majorization (by definition of `R₂` at an arrow).

\begin{code}

R₂-app : {σ τ : type} (F : B-Set⟦ σ ⇒ τ ⟧) (G : B-Set⟦ σ ⟧)
         (φ : Maj₂ (σ ⇒ τ)) (p : Maj₂ σ)
       → R₂ (σ ⇒ τ) F φ → R₂ σ G p → R₂ τ (F G) (φ p)
R₂-app F G φ p rF rG = rF G p rG

\end{code}
