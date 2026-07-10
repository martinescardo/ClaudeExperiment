A fundamental theorem: unconditional `height < ε₀` for first-order System T
with the recursor and `S` (except ground-`S` with function-typed components).

`MultHereditary` closed the hereditary predicate `𝔅M` on application, `K`, the
base combinators, the **recursor** `Iter`, the higher-type `S`-diagonal, and the
ground `S`-diagonal at `ι`. Here those closures are assembled into a fundamental
theorem and connected to actual dialogue height.

The observation that makes a *combinatory* fundamental theorem possible: the `S`
combinator's goodness `𝔅M (S-type) μ-S` closes at exactly the instances
`MultHereditary` handles. At `((ι⇒ι⇒ι)⇒(ι⇒ι)⇒ι⇒ι)` (ground `S` at `ι`) both
non-shared arguments and the shared one are recorded in `FunArgs`, and what
remains is the ground diagonal `𝔅M-S-ground-ι`. At any
`(((ρ₁⇒ρ₂)⇒σ⇒τ)⇒((ρ₁⇒ρ₂)⇒σ)⇒(ρ₁⇒ρ₂)⇒τ)` (shared argument a function type) it is
`𝔅M-S-higher`. Only ground `S` with a *function-typed* `σ` or `τ` — the shared
argument `ι`, another argument higher — is missing (the persistent structural
wall, the shared ground argument feeding a function-valued position that varies
with it, which `FunArgs` fixes before quantifying the ground argument).

The fragment `T★` therefore has `S` at those two instance families
(`Sg★`, `Sh★`), alongside `Ω/Zero/Succ/Iter/K/·`. Its terms embed into `T₁`
(`Majorant`), so `Majorant.height-≤-μ` gives `height ⟦ t ⟧ ≤ μ t`, and `𝔅M`
gives `μ t < ε₀`; hence `height ⟦ t ⟧ < ε₀` unconditionally. This is the first
fundamental theorem to include the recursor *and* `S` at higher types with the
`ε₀` bound — the recursor being the previously-open half.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryT
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import EffectfulForcing.MFPSAndVariations.Dialogue using (generic)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe using (height ; _≤_ ; ≤-trans ; ≤-S)
open import Claude.BrouwerOrdinals.Epsilon0 fe using (_<_ ; ε₀)
open import Claude.DialogueTreeHeight.Majorant fe
 using (T₁ ; Ω₁ ; Zero₁ ; Succ₁ ; Iter₁ ; K₁ ; S₁ ; _·₁_ ; ⟦_⟧₁ ; μ ; μ-S ;
        height-≤-μ)
open import Claude.DialogueTreeHeight.MultHereditary fe
 using (𝔅M ; 𝔅M-Ω ; 𝔅M-Zero ; 𝔅M-Succ ; 𝔅M-Iter ; 𝔅M-K ; 𝔅M-app ;
        𝔅M-S-ground-ι ; 𝔅M-S-higher ; 𝔅Mι-to-<ε₀)

\end{code}

The two `S` combinator instances that close, as goodness lemmas — each just
peels the `FunArgs` tuple and hands off to the corresponding `MultHereditary`
diagonal.

\begin{code}

𝔅M-Sg : 𝔅M ((ι ⇒ ι ⇒ ι) ⇒ (ι ⇒ ι) ⇒ ι ⇒ ι) μ-S
𝔅M-Sg ((φ , hφ) , ((γ , hγ) , ⋆)) = 𝔅M-S-ground-ι φ γ hφ hγ ⋆

𝔅M-Sh : {ρ₁ ρ₂ σ τ : type}
      → 𝔅M (((ρ₁ ⇒ ρ₂) ⇒ σ ⇒ τ) ⇒ ((ρ₁ ⇒ ρ₂) ⇒ σ) ⇒ (ρ₁ ⇒ ρ₂) ⇒ τ) μ-S
𝔅M-Sh ((φ , hφ) , ((γ , hγ) , rest)) = 𝔅M-S-higher φ γ hφ hγ rest

\end{code}

The fragment `T★`: first-order combinatory System T with `S` restricted to the
ground-`ι` and higher-type instances. It embeds into `T₁` by mapping both `S`
constructors to `S₁`.

\begin{code}

data T★ : type → 𝓤₀ ̇ where
 Ω★    : T★ (ι ⇒ ι)
 Zero★ : T★ ι
 Succ★ : T★ (ι ⇒ ι)
 Iter★ : T★ ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι)
 K★    : {σ τ : type} → T★ (σ ⇒ τ ⇒ σ)
 Sg★   : T★ ((ι ⇒ ι ⇒ ι) ⇒ (ι ⇒ ι) ⇒ ι ⇒ ι)
 Sh★   : {ρ₁ ρ₂ σ τ : type}
       → T★ (((ρ₁ ⇒ ρ₂) ⇒ σ ⇒ τ) ⇒ ((ρ₁ ⇒ ρ₂) ⇒ σ) ⇒ (ρ₁ ⇒ ρ₂) ⇒ τ)
 _·★_  : {σ τ : type} → T★ (σ ⇒ τ) → T★ σ → T★ τ

infixl 6 _·★_

e : {σ : type} → T★ σ → T₁ σ
e Ω★        = Ω₁
e Zero★     = Zero₁
e Succ★     = Succ₁
e Iter★     = Iter₁
e K★        = K₁
e Sg★       = S₁
e Sh★       = S₁
e (t ·★ u)  = e t ·₁ e u

\end{code}

The fundamental theorem: every `T★` majorant is good. Each case is one of the
`MultHereditary` closures; the application case is `𝔅M-app`, and the two `S`
cases are the lemmas above.

\begin{code}

goodμ : {σ : type} (t : T★ σ) → 𝔅M σ (μ (e t))
goodμ Ω★              = 𝔅M-Ω
goodμ Zero★           = 𝔅M-Zero
goodμ Succ★           = 𝔅M-Succ
goodμ Iter★           = 𝔅M-Iter
goodμ (K★ {σ} {τ})    = 𝔅M-K {σ} {τ}
goodμ Sg★             = 𝔅M-Sg
goodμ (Sh★ {ρ₁} {ρ₂} {σ} {τ}) = 𝔅M-Sh {ρ₁} {ρ₂} {σ} {τ}
goodμ (t ·★ u)        = 𝔅M-app _ _ (μ (e t)) (μ (e u)) (goodμ t) (goodμ u)

\end{code}

Hence the majorant of a ground `T★` term is `< ε₀`, and — via
`Majorant.height-≤-μ` — so is its dialogue-tree height, unconditionally.

\begin{code}

μ-<-ε₀ : (t : T★ ι) → μ (e t) < ε₀
μ-<-ε₀ t = 𝔅Mι-to-<ε₀ (μ (e t)) (goodμ t)

height-<-ε₀ : (t : T★ ι) → height ⟦ e t ⟧₁ < ε₀
height-<-ε₀ t = ≤-trans (≤-S (height-≤-μ (e t))) (μ-<-ε₀ t)

\end{code}

In particular the dialogue tree `⟦ e t ⟧₁ generic` of a first-order functional
`t : T★ ((ι ⇒ ι) ⇒ ι)` has height `< ε₀`.

\begin{code}

dialogue-height-<-ε₀ : (t : T★ ((ι ⇒ ι) ⇒ ι))
                     → height (⟦ e t ⟧₁ generic) < ε₀
dialogue-height-<-ε₀ t = height-<-ε₀ (t ·★ Ω★)

\end{code}
