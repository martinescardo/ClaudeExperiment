Design E: transformer-valued bounds — closing ground-`S` at a function type for
**super-linear** companions (beyond `MultHereditaryB`).

`MultHereditaryB` (Design B) closes ground-`S` `λ a → φ a (γ a)` with a
function-valued `γ a`, but only when the whole thing is bounded *linearly* in the
common weight: its data is a fixed multiplier `Mφ ⊗ Mγ`, so `(weight ⊕ c) ⊗ M`.
That already fails to even *express* a functional like `γ a = λ x → a ⊗ x`, whose
ground-`S` diagonal is `φ a (γ a) = a ⊗ (a ⊗ a) = a³` — genuinely super-linear in
`a`. Such a `γ` is not "good" in B's sense at all (no fixed `M` bounds `a ⊗ x`
for all `a`).

This module replaces the fixed multiplier by a **monotone, `< ε₀`-preserving
transformer** `T : 𝓑 → 𝓑` (`ValidT`). The bound at ground is `a ≤ T w`; function
arguments carry their own transformer `Tg`, and the result transformer is the
**composition** `T ∘ Tg`. Because composition of monotone `< ε₀`-preserving maps
is again one, application (`Good-app-fun`) and ground-`S` at a function type
(`Good-S-fun`) close — now for *arbitrary* `ValidT` companions, including
super-linear ones (`ValidT-sq : ValidT (λ w → w ⊗ w)` is exhibited). This is a
strict extension of B's reach.

Honest scope — the duality is *not* dissolved. Transformers fix the bound
*shape* (super-linear), not the *quantification order*. The irreducible fork,
unchanged from A/B: a function argument is required good either **at the same
weight `w`** (as here and in B — ground-`S` closes, the **recursor does not**,
because iterating `g` runs it past `w`) or **globally `∀ w'`** (as in A —
recursor closes, ground-`S` does not, because `γ a` is good only at weights
`≥ a`). No transformer bridges `w' < a`. So Design E = "B, super-linear": it
extends the ground-`S`/application reach to super-linear bounds but inherits B's
recursor gap. Closing that gap still requires the order-free,
ground-context-dependent Howard–Bezem predicate.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryE
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe using (_⊗_)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; S-<-ε₀ ; ⊗-mono-left ; ⊗-mono-right)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (⊗-<-ε₀)
open import Claude.BrouwerOrdinals.AffineClosure fe using (Z<ε₀)
open import Claude.DialogueTreeHeight.Majorant fe using (Maj)

\end{code}

A valid transformer: monotone and `< ε₀`-preserving. This is non-circular
(no orbit-closure is asserted — that is exactly the recursor's residual) and is
closed under composition, which is all the application/`S` closures need.

\begin{code}

ValidT : (𝓑 → 𝓑) → 𝓤₀ ̇
ValidT T = ((w : 𝓑) → w < ε₀ → T w < ε₀)
         × ((w w′ : 𝓑) → w ≤ w′ → T w ≤ T w′)

ValidT-id : ValidT (λ w → w)
ValidT-id = (λ w w<ε₀ → w<ε₀) , (λ w w′ w≤w′ → w≤w′)

ValidT-S : ValidT (λ w → S w)
ValidT-S = (λ w → S-<-ε₀ w) , (λ w w′ w≤w′ → ≤-S w≤w′)

ValidT-∘ : {T Tg : 𝓑 → 𝓑} → ValidT T → ValidT Tg → ValidT (λ w → T (Tg w))
ValidT-∘ {T} {Tg} (Tpres , Tmono) (Tgpres , Tgmono) =
   (λ w w<ε₀ → Tpres (Tg w) (Tgpres w w<ε₀))
 , (λ w w′ w≤w′ → Tmono (Tg w) (Tg w′) (Tgmono w w′ w≤w′))

\end{code}

A concrete **super-linear** valid transformer: `w ↦ w ⊗ w`. This is the shape B
could not carry (no fixed multiplier bounds `a ⊗ x` for all `a`); here it is a
first-class transformer, exhibiting that Design E handles companions strictly
beyond B.

\begin{code}

ValidT-sq : ValidT (λ w → w ⊗ w)
ValidT-sq =
   (λ w w<ε₀ → ⊗-<-ε₀ w w w<ε₀ w<ε₀)
 , (λ w w′ w≤w′ → ≤-trans (⊗-mono-left w≤w′ w) (⊗-mono-right w′ w≤w′))

\end{code}

The relation. Ground: `a ≤ T w`. Ground argument: bounded by the weight `w`,
same transformer. Function argument: carries its own valid transformer `Tg`,
required good at the *same* weight `w`, and the result transformer is `T ∘ Tg`.

\begin{code}

Bnd : (σ : type) → 𝓑 → (𝓑 → 𝓑) → Maj σ → 𝓤₀ ̇
Bnd ι              w T a = a ≤ T w
Bnd (ι ⇒ τ)        w T φ = (x : 𝓑) → x ≤ w → Bnd τ w T (φ x)
Bnd ((σ ⇒ σ') ⇒ τ) w T φ =
 (g : Maj (σ ⇒ σ')) (Tg : 𝓑 → 𝓑) → ValidT Tg
 → Bnd (σ ⇒ σ') w Tg g → Bnd τ w (λ u → T (Tg u)) (φ g)

Good : (σ : type) → Maj σ → 𝓤₀ ̇
Good σ φ = Σ T ꞉ (𝓑 → 𝓑) , ValidT T × ((w : 𝓑) → Bnd σ w T φ)

\end{code}

Ground extraction: at `ι`, `Good` gives `< ε₀` (evaluate the transformer at
`w = Z`, using `< ε₀`-preservation).

\begin{code}

Good-ι-to-<ε₀ : (a : 𝓑) → Good ι a → a < ε₀
Good-ι-to-<ε₀ a (T , (Tpres , Tmono) , bnd) =
 ≤-trans (≤-S (bnd Z)) (Tpres Z Z<ε₀)

\end{code}

The base combinators.

\begin{code}

Good-Zero : Good ι Z
Good-Zero = (λ w → w) , ValidT-id , (λ w → ≤-Z)

Good-Succ : Good (ι ⇒ ι) (λ a → a)
Good-Succ = (λ w → w) , ValidT-id , (λ w x x≤w → x≤w)

Good-Ω : Good (ι ⇒ ι) (λ a → S a)
Good-Ω = (λ w → S w) , ValidT-S , (λ w x x≤w → ≤-S x≤w)

\end{code}

Application at a function argument: the result transformer is the composition of
`F`'s and `G`'s.

\begin{code}

Good-app-fun : (σ σ' τ : type) (F : Maj ((σ ⇒ σ') ⇒ τ)) (G : Maj (σ ⇒ σ'))
             → Good ((σ ⇒ σ') ⇒ τ) F → Good (σ ⇒ σ') G → Good τ (F G)
Good-app-fun σ σ' τ F G (TF , vF , bF) (TG , vG , bG) =
 (λ u → TF (TG u)) , ValidT-∘ vF vG , (λ w → bF w G TG vG (bG w))

\end{code}

The headline: ground-`S` at a function type, for an **arbitrary** valid
transformer companion (super-linear included). The diagonal's transformer is
`Tφ ∘ Tγ` — where `Tγ` may be `λ w → w ⊗ w`, giving the cubic bound B could not
carry.

\begin{code}

Good-S-fun : (ρ ρ' τ : type)
             (φ : Maj (ι ⇒ (ρ ⇒ ρ') ⇒ τ)) (γ : Maj (ι ⇒ (ρ ⇒ ρ')))
           → Good (ι ⇒ (ρ ⇒ ρ') ⇒ τ) φ → Good (ι ⇒ (ρ ⇒ ρ')) γ
           → Good (ι ⇒ τ) (λ a → φ a (γ a))
Good-S-fun ρ ρ' τ φ γ (Tφ , vφ , bφ) (Tγ , vγ , bγ) =
 (λ u → Tφ (Tγ u)) , ValidT-∘ vφ vγ ,
 (λ w a a≤w → bφ w a a≤w (γ a) Tγ vγ (bγ w a a≤w))

\end{code}

And its `< ε₀` payoff at ground result: the diagonal applied to a `< ε₀`
argument is `< ε₀`, even for a super-linear companion.

\begin{code}

Good-S-fun-<ε₀ : (ρ ρ' : type)
                 (φ : Maj (ι ⇒ (ρ ⇒ ρ') ⇒ ι)) (γ : Maj (ι ⇒ (ρ ⇒ ρ')))
               → Good (ι ⇒ (ρ ⇒ ρ') ⇒ ι) φ → Good (ι ⇒ (ρ ⇒ ρ')) γ
               → (a : 𝓑) → a < ε₀ → φ a (γ a) < ε₀
Good-S-fun-<ε₀ ρ ρ' φ γ hφ hγ a a<ε₀ with Good-S-fun ρ ρ' ι φ γ hφ hγ
... | (T , (Tpres , Tmono) , bnd) =
 ≤-trans (≤-S (bnd a a (≤-refl a))) (Tpres a a<ε₀)

\end{code}
