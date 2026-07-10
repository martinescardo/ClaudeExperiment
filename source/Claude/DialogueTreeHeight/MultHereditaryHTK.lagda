The `K`-extended iterator-fragment fundamental theorem over the Howard
tower: unconditional `height < ε₀` for the fragment `TK` of combinatory
System T with `Ω / Zero / Succ / Iter / K / application`.

This strictly extends `MultHereditaryHT`'s `TI` (which lacked `K`) with the
constant combinator, now that `GoodH-K` (`MultHereditaryH7`) is proved fully
polymorphic. Every construct's `GoodH` closure is in hand, so the
fundamental theorem is again a short induction and the height payoffs follow
through `Majorant.height-≤-μ`.

Honest scope: `TK` omits `S`; its tower packs (`MultHereditaryH8`'s verified
diagonal core, `MultHereditaryH9`'s verified outer-multiplier absorption,
and the remaining `pack2`/`packS`/assembly) are the last construction for
the `T₁`-complete theorem. The conjecture for full System T (higher-type
recursion) remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryHTK
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
 using (T₁ ; Ω₁ ; Zero₁ ; Succ₁ ; Iter₁ ; K₁ ; _·₁_ ; ⟦_⟧₁ ; μ ; height-≤-μ)
open import Claude.DialogueTreeHeight.MultHereditaryH4 fe
 using (GoodH ; GoodH-ι-to-<ε₀ ; GoodH-Zero ; GoodH-Succ ; GoodH-Ω ;
        GoodH-app)
open import Claude.DialogueTreeHeight.MultHereditaryH6 fe
 using (GoodH-Iter)
open import Claude.DialogueTreeHeight.MultHereditaryH7 fe
 using (GoodH-K)

\end{code}

The fragment and its embedding into `T₁`.

\begin{code}

data TK : type → 𝓤₀ ̇ where
 ΩK    : TK (ι ⇒ ι)
 ZeroK : TK ι
 SuccK : TK (ι ⇒ ι)
 IterK : TK ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι)
 KK    : {σ τ : type} → TK (σ ⇒ τ ⇒ σ)
 _·K_  : {σ τ : type} → TK (σ ⇒ τ) → TK σ → TK τ

infixl 6 _·K_

e : {σ : type} → TK σ → T₁ σ
e ΩK       = Ω₁
e ZeroK    = Zero₁
e SuccK    = Succ₁
e IterK    = Iter₁
e KK       = K₁
e (t ·K u) = e t ·₁ e u

\end{code}

The fundamental theorem and the payoffs.

\begin{code}

goodμ : {σ : type} (t : TK σ) → GoodH σ (μ (e t))
goodμ ΩK             = GoodH-Ω
goodμ ZeroK          = GoodH-Zero
goodμ SuccK          = GoodH-Succ
goodμ IterK          = GoodH-Iter
goodμ (KK {σ} {τ})   = GoodH-K {σ} {τ}
goodμ (t ·K u)       = GoodH-app _ _ (μ (e t)) (μ (e u)) (goodμ t) (goodμ u)

μ-<-ε₀ : (t : TK ι) → μ (e t) < ε₀
μ-<-ε₀ t = GoodH-ι-to-<ε₀ (μ (e t)) (goodμ t)

height-<-ε₀ : (t : TK ι) → height ⟦ e t ⟧₁ < ε₀
height-<-ε₀ t = ≤-trans (≤-S (height-≤-μ (e t))) (μ-<-ε₀ t)

dialogue-height-<-ε₀ : (t : TK ((ι ⇒ ι) ⇒ ι))
                     → height (⟦ e t ⟧₁ generic) < ε₀
dialogue-height-<-ε₀ t = height-<-ε₀ (t ·K ΩK)

\end{code}
