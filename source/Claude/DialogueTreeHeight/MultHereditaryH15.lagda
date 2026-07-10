Design H, stage 2d(ix): `GoodH-S` — the `S` combinator over the Howard
tower (ground shared argument, middle and result), and the fundamental
theorem for the fragment `TS` that adds it to the iterator + `K` fragment.

With all three packs verified (`packδ`, `pack2`, `packS`), the `S` tower
datum `kS = (FS , packS)` exists, and `GoodH-S` assembles: the transformer
is Design F's `λ Tφ Tγ Ta → Tφ Ta (Tγ Ta)`; the `LT` maps thread the
argument data through it exactly as Design F's `Good-S`, carrying the
tower data `FS kφ` / `F2 kφ kγ` (the diagonal) at each partial application;
and — the point — the `BndH` component closes in *one line* from the
arguments' own `BndH`s, because the diagonal `Fδ ka = pr₁ (pr₁ kφ ka)
(pr₁ kγ ka)` is exactly the composition the bound relation feeds. The `BndL`
majorant bound is Design F's `Good-S` verbatim.

Fragment `TS`: `Ω/Zero/Succ/Iter/K/S/·` with `S` at `ρ = σ = τ = ι`. Honest
scope: this `S` instance is the all-ground one; higher-`σ`/`τ` `S` (built in
`MultHereditaryFNT`'s `T₃` for the *Design-F* predicate, and needing the
`n`-ary joint data on the tower) is not yet ported to Design H. The
conjecture for full System T remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryH15
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
 using (Maj ; μ-S ;
        T₁ ; Ω₁ ; Zero₁ ; Succ₁ ; Iter₁ ; K₁ ; S₁ ; _·₁_ ; ⟦_⟧₁ ; μ ;
        height-≤-μ)
open import Claude.DialogueTreeHeight.MultHereditaryF fe
 using (𝕋 ; GoodT)
open import Claude.DialogueTreeHeight.MultHereditaryH fe using (𝕂)
open import Claude.DialogueTreeHeight.MultHereditaryH4 fe
 using (BndH ; LT ; BndL ; GoodH ; GoodH-ι-to-<ε₀ ; GoodH-Zero ; GoodH-Succ ;
        GoodH-Ω ; GoodH-app)
open import Claude.DialogueTreeHeight.MultHereditaryH6 fe
 using (GoodH-Iter)
open import Claude.DialogueTreeHeight.MultHereditaryH7 fe
 using (GoodH-K)
open import Claude.DialogueTreeHeight.MultHereditaryH13 fe
 using (module Spack2)
open import Claude.DialogueTreeHeight.MultHereditaryH14 fe
 using (FS ; module SpackS)

\end{code}

The `S` combinator's tower goodness.

\begin{code}

GoodH-S : GoodH ((ι ⇒ ι ⇒ ι) ⇒ (ι ⇒ ι) ⇒ ι ⇒ ι) μ-S
GoodH-S = Tr , (maps , (kS , bndH)) , bndL
 where
  Tr : 𝕋 ((ι ⇒ ι ⇒ ι) ⇒ (ι ⇒ ι) ⇒ ι ⇒ ι)
  Tr = λ Tφ Tγ Ta → (Tφ Ta) (Tγ Ta)

  kS : 𝕂 ((ι ⇒ ι ⇒ ι) ⇒ ((ι ⇒ ι) ⇒ (ι ⇒ ι)))
  kS = FS , SpackS.packS

  bndH : BndH ((ι ⇒ ι ⇒ ι) ⇒ (ι ⇒ ι) ⇒ ι ⇒ ι) Tr kS
  bndH Tφ kφ bndφ g kg bndg a ka bnda =
   bndφ a ka bnda (g a) (pr₁ kg ka) (bndg a ka bnda)

  maps : (Tφ : 𝕋 (ι ⇒ ι ⇒ ι)) → LT (ι ⇒ ι ⇒ ι) Tφ
       → LT ((ι ⇒ ι) ⇒ ι ⇒ ι) (Tr Tφ)
  maps Tφ (mφ , kφ , bndφ) = m1 , (FS kφ , b1)
   where
    b1 : BndH ((ι ⇒ ι) ⇒ ι ⇒ ι) (Tr Tφ) (FS kφ)
    b1 g kg bndg a ka bnda =
     bndφ a ka bnda (g a) (pr₁ kg ka) (bndg a ka bnda)

    m1 : (Tγ : 𝕋 (ι ⇒ ι)) → LT (ι ⇒ ι) Tγ
       → LT (ι ⇒ ι) (Tr Tφ Tγ)
    m1 Tγ (mγ , kγ , bndγ) = m2 , (Spack2.F2 kφ kγ , b2)
     where
      m2 : (Ta : 𝕋 ι) → GoodT ι Ta → GoodT ι (Tr Tφ Tγ Ta)
      m2 Ta gTa = pr₁ (mφ Ta gTa) (Tγ Ta) (mγ Ta gTa)

      b2 : BndH (ι ⇒ ι) (Tr Tφ Tγ) (Spack2.F2 kφ kγ)
      b2 a ka bnda =
       bndφ a ka bnda (Tγ a) (pr₁ kγ ka) (bndγ a ka bnda)

  bndL : (w : 𝓑) → BndL ((ι ⇒ ι ⇒ ι) ⇒ (ι ⇒ ι) ⇒ ι ⇒ ι) w Tr μ-S
  bndL w φ Tφ lTφ φ-glob γ Tγ lTγ γ-glob a Ta lTa a-glob =
   φ-glob w a Ta lTa a-glob (γ a) (Tγ Ta) (pr₁ lTγ Ta lTa)
     (λ w′ → γ-glob w′ a Ta lTa a-glob)

\end{code}

The fragment `TS` and its fundamental theorem.

\begin{code}

data TS : type → 𝓤₀ ̇ where
 ΩS    : TS (ι ⇒ ι)
 ZeroS : TS ι
 SuccS : TS (ι ⇒ ι)
 IterS : TS ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι)
 KS    : {σ τ : type} → TS (σ ⇒ τ ⇒ σ)
 SS    : TS ((ι ⇒ ι ⇒ ι) ⇒ (ι ⇒ ι) ⇒ ι ⇒ ι)
 _·S_  : {σ τ : type} → TS (σ ⇒ τ) → TS σ → TS τ

infixl 6 _·S_

e : {σ : type} → TS σ → T₁ σ
e ΩS       = Ω₁
e ZeroS    = Zero₁
e SuccS    = Succ₁
e IterS    = Iter₁
e KS       = K₁
e SS       = S₁
e (t ·S u) = e t ·₁ e u

goodμ : {σ : type} (t : TS σ) → GoodH σ (μ (e t))
goodμ ΩS           = GoodH-Ω
goodμ ZeroS        = GoodH-Zero
goodμ SuccS        = GoodH-Succ
goodμ IterS        = GoodH-Iter
goodμ (KS {σ} {τ}) = GoodH-K {σ} {τ}
goodμ SS           = GoodH-S
goodμ (t ·S u)     = GoodH-app _ _ (μ (e t)) (μ (e u)) (goodμ t) (goodμ u)

μ-<-ε₀ : (t : TS ι) → μ (e t) < ε₀
μ-<-ε₀ t = GoodH-ι-to-<ε₀ (μ (e t)) (goodμ t)

height-<-ε₀ : (t : TS ι) → height ⟦ e t ⟧₁ < ε₀
height-<-ε₀ t = ≤-trans (≤-S (height-≤-μ (e t))) (μ-<-ε₀ t)

dialogue-height-<-ε₀ : (t : TS ((ι ⇒ ι) ⇒ ι))
                     → height (⟦ e t ⟧₁ generic) < ε₀
dialogue-height-<-ε₀ t = height-<-ε₀ (t ·S ΩS)

\end{code}
