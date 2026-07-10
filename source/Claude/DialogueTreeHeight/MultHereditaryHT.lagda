Design H, first payoff: the iterator-fragment fundamental theorem over the
Howard tower — unconditional `height < ε₀` for the fragment `TI` of
combinatory System T with `Ω / Zero / Succ / Iter / application`.

This is the tower's end-to-end validation: the fragment has arbitrarily
nested, oracle-driven ground recursion (`Iter (Iter … ) …`, counts computed
by dialogue with the oracle), and every construct's `GoodH` closure is
proved in modules 51 and 53 — so the fundamental theorem is a four-line
induction, and the height payoffs follow through `Majorant.height-≤-μ` as
always. Each recursor nesting costs three bumps over its argument's budget
(module 53's budget identity), so the heights climb exactly the
`ω`-exponent tower, staying below `ε₀`.

Honest scope: `TI` omits `K` and `S` — their tower packs (a `reflect` +
rebase for `K`; the `PackDom`-driven diagonal rebase for `S`) are the two
remaining constructions for the `T₁`-complete theorem, with the machinery
(modules 48–50) proven and waiting. The conjecture for full System T
(higher-type recursion) remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryHT
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import EffectfulForcing.MFPSAndVariations.Dialogue using (generic)
open import Claude.DialogueTreeHeight.Constructive fe
 using (height ; _≤_ ; ≤-trans ; ≤-S)
open import Claude.BrouwerOrdinals.Epsilon0 fe using (_<_ ; ε₀)
open import Claude.DialogueTreeHeight.Majorant fe
 using (T₁ ; Ω₁ ; Zero₁ ; Succ₁ ; Iter₁ ; _·₁_ ; ⟦_⟧₁ ; μ ; height-≤-μ)
open import Claude.DialogueTreeHeight.MultHereditaryH4 fe
 using (GoodH ; GoodH-ι-to-<ε₀ ; GoodH-Zero ; GoodH-Succ ; GoodH-Ω ;
        GoodH-app)
open import Claude.DialogueTreeHeight.MultHereditaryH6 fe
 using (GoodH-Iter)

\end{code}

The fragment and its embedding into `T₁`.

\begin{code}

data TI : type → 𝓤₀ ̇ where
 ΩI    : TI (ι ⇒ ι)
 ZeroI : TI ι
 SuccI : TI (ι ⇒ ι)
 IterI : TI ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι)
 _·I_  : {σ τ : type} → TI (σ ⇒ τ) → TI σ → TI τ

infixl 6 _·I_

e : {σ : type} → TI σ → T₁ σ
e ΩI       = Ω₁
e ZeroI    = Zero₁
e SuccI    = Succ₁
e IterI    = Iter₁
e (t ·I u) = e t ·₁ e u

\end{code}

The fundamental theorem and the payoffs.

\begin{code}

goodμ : {σ : type} (t : TI σ) → GoodH σ (μ (e t))
goodμ ΩI       = GoodH-Ω
goodμ ZeroI    = GoodH-Zero
goodμ SuccI    = GoodH-Succ
goodμ IterI    = GoodH-Iter
goodμ (t ·I u) = GoodH-app _ _ (μ (e t)) (μ (e u)) (goodμ t) (goodμ u)

μ-<-ε₀ : (t : TI ι) → μ (e t) < ε₀
μ-<-ε₀ t = GoodH-ι-to-<ε₀ (μ (e t)) (goodμ t)

height-<-ε₀ : (t : TI ι) → height ⟦ e t ⟧₁ < ε₀
height-<-ε₀ t = ≤-trans (≤-S (height-≤-μ (e t))) (μ-<-ε₀ t)

dialogue-height-<-ε₀ : (t : TI ((ι ⇒ ι) ⇒ ι))
                     → height (⟦ e t ⟧₁ generic) < ε₀
dialogue-height-<-ε₀ t = height-<-ε₀ (t ·I ΩI)

\end{code}
