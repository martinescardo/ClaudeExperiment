Design B: an s-relative logical relation — closing ground-`S` at a
function-typed argument (the case `MultHereditary` could not reach).

`MultHereditary` (Design A) uses the `Hereditary` skeleton: function arguments
are *global* majorants recorded in `FunArgs`, quantified before the common bound
`s`. That closes application at every type, the recursor, `K`, `S`-higher and
ground-`S` at `ι` — but it cannot close ground-`S` when the shared argument's
companion is *function-typed* (`λ a → φ a (γ a)` with `γ a` a function of the
ground `a`): a global majorant of the varying `γ a` does not exist, because `φ`
can probe its function argument outside any fixed range `[0,s]`.

This module is the dual design. Instead of global majorants it uses an
**`s`-relative logical relation** `Bnd σ s c M φ`: ground arguments are measured
against the common bound `s` keeping the same data `(c,M)`, and *function*
arguments carry their **own** data `(cg,Mg)` which threads into the result
multiplicatively, `M ⊗ Mg` — exactly `MultDominated.MDom-∘`'s behaviour. Because
a function argument is fed with its actual `s`-relative bound (not a global
majorant), ground-`S` at a function type closes directly and *without* any
monotonicity hypothesis: `γ a` is handed to `φ a` with `γ`'s own data, giving
multiplier `Mφ ⊗ Mγ` (`Good-S-fun`). Application at a *function* argument closes
the same way (`Good-app-fun`).

The dual gaps (honest scope). The `s`-relative bound on a function argument
holds only for inputs `≤ s`, so it cannot bound anything that probes the
argument *outside* `[0,s]`. Two things do: the **recursor** (iterating `g` runs
`g` on `iter g a k > s`) and **ground-argument application** when a ground
argument precedes a function argument (re-indexing up to a larger bound then
needs a function argument good at the larger bound, which the caller supplies
only at the smaller one — `Bnd` is antitone in `s` at function-argument slots).
These are precisely the cases Design A closes. So A and B are complementary:
each closes what the other cannot, neither alone is a full fundamental theorem.
The shared obstruction — a single relation that is `s`-relative *and*
order-insensitive *and* lets a function-argument bound depend on the preceding
ground context — is the genuine Howard–Bezem strong-majorizability step.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryB
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe using (ι[_] ; ω ; _⊗_)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; Z-left-unit ; ⊕-increasing-right ; ⊕-<-ε₀)
open import Claude.BrouwerOrdinals.Affine fe using (⊕-increasing-left)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (⊗-<-ε₀)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (x-≤-x⊗ ; Z<ε₀ ; ι<ε₀)
open import Claude.BrouwerOrdinals.MultAffine fe using (ω-pos)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; ω-valid ; validMult-⊗)
open import Claude.DialogueTreeHeight.Majorant fe using (Maj)

\end{code}

The `s`-relative relation. At `ι` the value is `≤ (s ⊕ c) ⊗ M`. At a ground
argument (`ι ⇒ τ`) the argument is bounded by the common `s` and the data is
unchanged. At a function argument (`(σ ⇒ σ') ⇒ τ`) the argument carries its own
valid data `(cg,Mg)`, and the result's data is `(c ⊕ cg , M ⊗ Mg)`.

\begin{code}

Bnd : (σ : type) → 𝓑 → 𝓑 → 𝓑 → Maj σ → 𝓤₀ ̇
Bnd ι              s c M a = a ≤ ((s ⊕ c) ⊗ M)
Bnd (ι ⇒ τ)        s c M φ = (x : 𝓑) → x ≤ s → Bnd τ s c M (φ x)
Bnd ((σ ⇒ σ') ⇒ τ) s c M φ =
 (g : Maj (σ ⇒ σ')) (cg Mg : 𝓑) → ValidMult Mg → cg < ε₀
 → Bnd (σ ⇒ σ') s cg Mg g → Bnd τ s (c ⊕ cg) (M ⊗ Mg) (φ g)

Good : (σ : type) → Maj σ → 𝓤₀ ̇
Good σ φ =
 Σ M ꞉ 𝓑 , ValidMult M × (Σ c ꞉ 𝓑 , (c < ε₀) × ((s : 𝓑) → Bnd σ s c M φ))

\end{code}

Ground extraction: at `ι`, `Good` is equivalent to `< ε₀` (take `s = Z`, giving
`c ⊗ M < ε₀`; conversely use `M = ω`, `c = a`).

\begin{code}

Good-ι-to-<ε₀ : (a : 𝓑) → Good ι a → a < ε₀
Good-ι-to-<ε₀ a (M , (M+ , dbl , M<ε₀) , c , c<ε₀ , bnd) =
 ≤-trans (≤-S (transport (a ≤_) (ap (_⊗ M) (Z-left-unit c)) (bnd Z)))
         (⊗-<-ε₀ c M c<ε₀ M<ε₀)

<ε₀-to-Good-ι : (a : 𝓑) → a < ε₀ → Good ι a
<ε₀-to-Good-ι a a<ε₀ =
 ω , ω-valid , a , a<ε₀ ,
 (λ s → ≤-trans (⊕-increasing-left s a) (x-≤-x⊗ (s ⊕ a) ω ω-pos))

\end{code}

The base combinators. `Zero`, `Succ` and `Ω` — the same leaves as elsewhere,
here in the `s`-relative form (`S s = s ⊕ ι[1]` definitionally).

\begin{code}

Good-Zero : Good ι Z
Good-Zero = <ε₀-to-Good-ι Z Z<ε₀

Good-Succ : Good (ι ⇒ ι) (λ a → a)
Good-Succ =
 ω , ω-valid , Z , Z<ε₀ ,
 (λ s x x≤s → ≤-trans x≤s
                (≤-trans (⊕-increasing-right s Z) (x-≤-x⊗ (s ⊕ Z) ω ω-pos)))

Good-Ω : Good (ι ⇒ ι) (λ a → S a)
Good-Ω =
 ω , ω-valid , ι[ 1 ] , ι<ε₀ 1 ,
 (λ s x x≤s → ≤-trans (≤-S x≤s) (x-≤-x⊗ (s ⊕ ι[ 1 ]) ω ω-pos))

\end{code}

Application at a **function** argument closes: `F`'s bound consumes `G` with
`G`'s own data, and the multiplier threads to `M_F ⊗ M_G`. (No re-indexing of
`s` is needed — the function argument is measured against the same `s`.)

\begin{code}

Good-app-fun : (σ σ' τ : type) (F : Maj ((σ ⇒ σ') ⇒ τ)) (G : Maj (σ ⇒ σ'))
             → Good ((σ ⇒ σ') ⇒ τ) F → Good (σ ⇒ σ') G → Good τ (F G)
Good-app-fun σ σ' τ F G
             (MF , vMF , cF , cF<ε₀ , bF) (MG , vMG , cG , cG<ε₀ , bG) =
 MF ⊗ MG , validMult-⊗ vMF vMG , cF ⊕ cG , ⊕-<-ε₀ cF cG cF<ε₀ cG<ε₀ ,
 (λ s → bF s G cG MG vMG cG<ε₀ (bG s))

\end{code}

The headline: ground-`S` at a **function-typed** companion closes. Given `φ` and
`γ` good, `λ a → φ a (γ a)` is good — `γ a` is fed to `φ a` as a function
argument with `γ`'s own data `(cγ, Mγ)`, the shared ground `a ≤ s` serving both.
The multiplier is `Mφ ⊗ Mγ`; no monotonicity of `φ` is assumed. This is the case
Design A (`MultHereditary`) provably could not close.

\begin{code}

Good-S-fun : (ρ ρ' τ : type)
             (φ : Maj (ι ⇒ (ρ ⇒ ρ') ⇒ τ)) (γ : Maj (ι ⇒ (ρ ⇒ ρ')))
           → Good (ι ⇒ (ρ ⇒ ρ') ⇒ τ) φ → Good (ι ⇒ (ρ ⇒ ρ')) γ
           → Good (ι ⇒ τ) (λ a → φ a (γ a))
Good-S-fun ρ ρ' τ φ γ
           (Mφ , vMφ , cφ , cφ<ε₀ , bφ) (Mγ , vMγ , cγ , cγ<ε₀ , bγ) =
 Mφ ⊗ Mγ , validMult-⊗ vMφ vMγ , cφ ⊕ cγ , ⊕-<-ε₀ cφ cγ cφ<ε₀ cγ<ε₀ ,
 (λ s a a≤s → bφ s a a≤s (γ a) cγ Mγ vMγ cγ<ε₀ (bγ s a a≤s))

\end{code}

The application dual to `Good-S-fun`: applying a functional to a good function
argument and reading off `< ε₀`.

\begin{code}

Good-app-fun-<ε₀ : (σ σ' : type) (F : Maj ((σ ⇒ σ') ⇒ ι)) (G : Maj (σ ⇒ σ'))
                 → Good ((σ ⇒ σ') ⇒ ι) F → Good (σ ⇒ σ') G → F G < ε₀
Good-app-fun-<ε₀ σ σ' F G hF hG =
 Good-ι-to-<ε₀ (F G) (Good-app-fun σ σ' ι F G hF hG)

\end{code}
