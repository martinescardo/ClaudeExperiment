Hereditary multiplier-dominated majorizability — the recursor closes.

Every prior hereditary predicate over first-order types
(`Hereditary`, `PolyHereditary`, `PolyTransformer`, `CNFTransformer`) closed
application, `K`, the higher-type diagonal of `S`, and the base combinators, but
left the fully hereditary **recursor** `Iter` open: closing it needs the
predicate on `ι ⇒ ι` functions to expose a shape that survives its own orbit,
and the affine shapes were not orbit-closed (the `ω`-multiplier escape) while the
abstract transformer dropped the shape entirely.

`MultDominated` supplied the missing shape: the multiplier-dominated class `MDom`
is closed under its own orbit (`MDom-orbit`, `MDom2-Iter`). This module runs the
`Hereditary`/`CNFTransformer` skeleton (`GroundType`, `FunArgs`, `plug`) with the
ground joint bound taken to be the `MDom` bound `(s ⊕ c) ⊗ M` for a `ValidMult`
`M`, rather than the finite affine `(s ⊕ d) ⊗ ι[m]`. The payoff is **`𝔅M-Iter`**:
the recursor majorant `μ-Iter` is good — the case none of the earlier predicates
could take — because at a function argument `g` the predicate hands back exactly
the `MDom` data `MDom2-Iter` consumes. Application, `K`, `S`-higher and the base
combinators port verbatim, and the **ground `S`-diagonal at `ι`** closes too
(`𝔅M-S-ground-ι`, via `MDom2-diag`).

Honest scope. This closes the hereditary predicate on application, `K`,
`S`-higher, the base combinators, the **recursor**, and the ground `S`-diagonal
*at type `ι`*. What is not yet here is a fundamental theorem over all of `T₁`:
the general ground `S`-diagonal (shared argument `ι`, but the two other arguments
at higher types) is the residual — the same combinatorial case open throughout,
now the *sole* gap, with the recursor (the previously-hard half) discharged.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditary
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left ; ⊕-assoc)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; Z-left-unit ; ⊕-increasing-right ; ⊕-<-ε₀ ;
        ⊗-mono-left ; ⊕-mono-right)
open import Claude.BrouwerOrdinals.Affine fe using (⊕-increasing-left)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (⊗-<-ε₀)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (x-≤-x⊗ ; Z<ε₀ ; ι<ε₀)
open import Claude.BrouwerOrdinals.MultAffine fe using (ω-pos)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; ω-valid ; MDom ; MDom2 ; MDom2-Iter ; MDom2-diag)
open import Claude.DialogueTreeHeight.Hereditary fe using (GroundType)
open import Claude.DialogueTreeHeight.Majorant fe using (Maj)

\end{code}

The ground joint bound, relative to a common upper bound `s` on all ground
arguments: the value is `≤ (s ⊕ c) ⊗ M` for a valid multiplier `M`. Structurally
this is `Hereditary.JB` with `ι[m] ↦ M` (a `ValidMult`).

\begin{code}

JBM : (σ : type) → Maj σ → 𝓑 → 𝓑 → 𝓑 → 𝓤₀ ̇
JBM ι              a s c M = a ≤ ((s ⊕ c) ⊗ M)
JBM (ι ⇒ τ)        φ s c M = (x : 𝓑) → x ≤ s → JBM τ (φ x) s c M
JBM ((σ ⇒ σ') ⇒ τ) φ s c M = 𝟘

JointM : (σ : type) → Maj σ → 𝓤₀ ̇
JointM σ φ =
 Σ M ꞉ 𝓑 , ValidMult M × (Σ c ꞉ 𝓑 , (c < ε₀) × ((s : 𝓑) → JBM σ φ s c M))

\end{code}

The function-argument assignments and the goodness predicate — verbatim the
`Hereditary`/`CNFTransformer` mutual recursion.

\begin{code}

mutual

 FunArgs : type → 𝓤₀ ̇
 FunArgs ι              = 𝟙
 FunArgs (ι ⇒ τ)        = FunArgs τ
 FunArgs ((σ ⇒ σ') ⇒ τ) = (Σ g ꞉ Maj (σ ⇒ σ') , 𝔅M (σ ⇒ σ') g) × FunArgs τ

 plug : (σ : type) → Maj σ → FunArgs σ → Maj (GroundType σ)
 plug ι              a _         = a
 plug (ι ⇒ τ)        φ fa        = λ x → plug τ (φ x) fa
 plug ((σ ⇒ σ') ⇒ τ) φ (gg , fa) = plug τ (φ (pr₁ gg)) fa

 𝔅M : (σ : type) → Maj σ → 𝓤₀ ̇
 𝔅M σ φ = (fa : FunArgs σ) → JointM (GroundType σ) (plug σ φ fa)

\end{code}

Ground extraction: at `ι`, `𝔅M` is equivalent to `< ε₀`. Forward, take the
common bound `s = Z` so the bound is `c ⊗ M < ε₀`; backward, use `M = ω` and
`c = a`.

\begin{code}

𝔅Mι-to-<ε₀ : (a : 𝓑) → 𝔅M ι a → a < ε₀
𝔅Mι-to-<ε₀ a good = h (good ⋆)
 where
  h : JointM ι a → a < ε₀
  h (M , (M+ , dbl , M<ε₀) , c , c<ε₀ , bnd) =
   ≤-trans (≤-S (transport (a ≤_) (ap (_⊗ M) (Z-left-unit c)) (bnd Z)))
           (⊗-<-ε₀ c M c<ε₀ M<ε₀)

<ε₀-to-𝔅Mι : (a : 𝓑) → a < ε₀ → 𝔅M ι a
<ε₀-to-𝔅Mι a a<ε₀ _ =
 ω , ω-valid , a , a<ε₀ ,
 (λ s → ≤-trans (⊕-increasing-left s a) (x-≤-x⊗ (s ⊕ a) ω ω-pos))

\end{code}

Conversions between the common-bound `JointM` at arity 1 and 2 and the
per-argument classes `MDom`/`MDom2` (they coincide: instantiate the common bound
to the argument for the forward direction, weaken by monotonicity for the
backward).

\begin{code}

JointM1→MDom : {g : 𝓑 → 𝓑} → JointM (ι ⇒ ι) g → MDom g
JointM1→MDom (M , vM , c , c<ε₀ , jb) =
 M , vM , c , c<ε₀ , (λ b → jb b b (≤-refl b))

MDom→JointM1 : {g : 𝓑 → 𝓑} → MDom g → JointM (ι ⇒ ι) g
MDom→JointM1 (M , vM , c , c<ε₀ , bnd) =
 M , vM , c , c<ε₀ ,
 (λ s x x≤s → ≤-trans (bnd x) (⊗-mono-left (⊕-mono-left x≤s c) M))

MDom2→JointM2 : {F : 𝓑 → 𝓑 → 𝓑} → MDom2 F → JointM (ι ⇒ ι ⇒ ι) F
MDom2→JointM2 (M , vM , c , c<ε₀ , jb2) =
 M , vM , c , c<ε₀ , (λ s a a≤s b b≤s → jb2 s a b a≤s b≤s)

JointM2→MDom2 : {F : 𝓑 → 𝓑 → 𝓑} → JointM (ι ⇒ ι ⇒ ι) F → MDom2 F
JointM2→MDom2 (M , vM , c , c<ε₀ , jb) =
 M , vM , c , c<ε₀ , (λ s a b a≤s b≤s → jb s a a≤s b b≤s)

\end{code}

The argument-shift lemma (verbatim `Hereditary.JB-shift`, `ι[m] ↦ M`): a common
bound `s ⊕ G` with constant `c` re-reads as bound `s` with constant `G ⊕ c`,
by associativity of `⊕`.

\begin{code}

JBM-shift : (σ : type) (φ : Maj σ) (s G c M : 𝓑)
          → JBM σ φ (s ⊕ G) c M → JBM σ φ s (G ⊕ c) M
JBM-shift ι              a s G c M h =
 transport (a ≤_) (ap (_⊗ M) (⊕-assoc s G c)) h
JBM-shift (ι ⇒ τ)        φ s G c M h =
 λ x x≤s → JBM-shift τ (φ x) s G c M
             (h x (≤-trans x≤s (⊕-increasing-right s G)))
JBM-shift ((σ ⇒ σ') ⇒ τ) φ s G c M h = h

\end{code}

Application closure (verbatim `Hereditary.𝔅-app`): a function argument feeds
through the `FunArgs` tuple; a ground argument is absorbed into the constant via
`JBM-shift`.

\begin{code}

𝔅M-app : (σ τ : type) (F : Maj (σ ⇒ τ)) (G : Maj σ)
       → 𝔅M (σ ⇒ τ) F → 𝔅M σ G → 𝔅M τ (F G)
𝔅M-app (σ ⇒ σ') τ F G hF hG fa = hF ((G , hG) , fa)
𝔅M-app ι         τ F G hF hG fa with hF fa
... | (M , vM , c , c<ε₀ , jbnd) =
 M , vM , (G ⊕ c) , ⊕-<-ε₀ G c (𝔅Mι-to-<ε₀ G hG) c<ε₀ ,
 (λ s → JBM-shift (GroundType τ) (plug τ (F G) fa) s G c M
          (jbnd (s ⊕ G) G (⊕-increasing-left s G)))

\end{code}

The base combinators. `Zero ↦ Z`; `Succ` the identity; `Ω` the successor
(`S s = s ⊕ ι[1]` definitionally).

\begin{code}

𝔅M-Zero : 𝔅M ι Z
𝔅M-Zero = <ε₀-to-𝔅Mι Z Z<ε₀

𝔅M-Succ : 𝔅M (ι ⇒ ι) (λ a → a)
𝔅M-Succ _ =
 ω , ω-valid , Z , Z<ε₀ ,
 (λ s x x≤s → ≤-trans x≤s
                (≤-trans (⊕-increasing-right s Z) (x-≤-x⊗ (s ⊕ Z) ω ω-pos)))

𝔅M-Ω : 𝔅M (ι ⇒ ι) (λ a → S a)
𝔅M-Ω _ =
 ω , ω-valid , ι[ 1 ] , ι<ε₀ 1 ,
 (λ s x x≤s → ≤-trans (≤-S x≤s) (x-≤-x⊗ (s ⊕ ι[ 1 ]) ω ω-pos))

\end{code}

Weakening and `K` (verbatim `CNFTransformer`).

\begin{code}

𝔅M-weaken : (τ σ : type) (φ : Maj σ) → 𝔅M σ φ → 𝔅M (τ ⇒ σ) (λ _ → φ)
𝔅M-weaken ι         σ φ hφ fa with hφ fa
... | (M , vM , c , c<ε₀ , bnd) = M , vM , c , c<ε₀ , (λ s y _ → bnd s)
𝔅M-weaken (τ₁ ⇒ τ₂) σ φ hφ ((h , hh) , fa'') = hφ fa''

𝔅M-K : {σ τ : type} → 𝔅M (σ ⇒ τ ⇒ σ) (λ a b → a)
𝔅M-K {ι} {ι} _ =
 ω , ω-valid , Z , Z<ε₀ ,
 (λ s x x≤s y _ → ≤-trans x≤s
                    (≤-trans (⊕-increasing-right s Z) (x-≤-x⊗ (s ⊕ Z) ω ω-pos)))
𝔅M-K {ι} {τ₁ ⇒ τ₂} ((h , hh) , _) =
 ω , ω-valid , Z , Z<ε₀ ,
 (λ s x x≤s → ≤-trans x≤s
                (≤-trans (⊕-increasing-right s Z) (x-≤-x⊗ (s ⊕ Z) ω ω-pos)))
𝔅M-K {σ₁ ⇒ σ₂} {τ} ((g , hg) , fa') = 𝔅M-weaken τ (σ₁ ⇒ σ₂) g hg fa'

\end{code}

The higher-type diagonal of `S` — three applications sharing the same function
argument (verbatim `CNFTransformer.𝔅pT-S-higher`).

\begin{code}

𝔅M-S-higher : {ρ₁ ρ₂ σ τ : type}
              (φ : Maj ((ρ₁ ⇒ ρ₂) ⇒ σ ⇒ τ)) (γ : Maj ((ρ₁ ⇒ ρ₂) ⇒ σ))
            → 𝔅M ((ρ₁ ⇒ ρ₂) ⇒ σ ⇒ τ) φ → 𝔅M ((ρ₁ ⇒ ρ₂) ⇒ σ) γ
            → 𝔅M ((ρ₁ ⇒ ρ₂) ⇒ τ) (λ a → φ a (γ a))
𝔅M-S-higher {ρ₁} {ρ₂} {σ} {τ} φ γ hφ hγ ((g , hg) , fa'') =
 𝔅M-app σ τ (φ g) (γ g)
   (𝔅M-app (ρ₁ ⇒ ρ₂) (σ ⇒ τ) φ g hφ hg)
   (𝔅M-app (ρ₁ ⇒ ρ₂) σ γ g hγ hg)
   fa''

\end{code}

The recursor — the case none of the earlier predicates could take. At the
function argument `g`, `𝔅M (ι ⇒ ι) g` yields (via `JointM1→MDom`) exactly the
`MDom` data that `MDom2-Iter` consumes, producing the joint bound for
`μ-Iter g = λ a ν → L (λ k → iter g a k) ⊕ ν`. So the recursor closes because the
`MDom` shape survives its own orbit.

\begin{code}

μ-Iter : (𝓑 → 𝓑) → 𝓑 → 𝓑 → 𝓑
μ-Iter g a ν = L (λ k → iter g a k) ⊕ ν

𝔅M-Iter : 𝔅M ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι) μ-Iter
𝔅M-Iter ((g , hg) , ⋆) =
 MDom2→JointM2 (MDom2-Iter (JointM1→MDom (hg ⋆)))

\end{code}

The ground `S`-diagonal at type `ι`: `λ a → φ a (γ a)` with `φ : ι ⇒ ι ⇒ ι`,
`γ : ι ⇒ ι`. This is the duplication case; it closes via `MDom2-diag` — the two
goodness proofs give `MDom2 φ` and `MDom γ`, and their diagonal is `MDom`.

\begin{code}

𝔅M-S-ground-ι : (φ : Maj (ι ⇒ ι ⇒ ι)) (γ : Maj (ι ⇒ ι))
              → 𝔅M (ι ⇒ ι ⇒ ι) φ → 𝔅M (ι ⇒ ι) γ
              → 𝔅M (ι ⇒ ι) (λ a → φ a (γ a))
𝔅M-S-ground-ι φ γ hφ hγ _ =
 MDom→JointM1
  (MDom2-diag (JointM2→MDom2 (hφ ⋆)) (JointM1→MDom (hγ ⋆)))

\end{code}
