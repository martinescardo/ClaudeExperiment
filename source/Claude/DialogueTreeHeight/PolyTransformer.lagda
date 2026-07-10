Hereditary poly-*transformer* majorizability (constructive) — past the affine
ground bound.

The `⊞`-based hereditary predicate `PolyHereditary` bounds a ground majorant,
relative to a common polynomial bound `ps` on the ground arguments, by the
*affine* polynomial `nmul k ps ⊞ d` — a fixed coefficient-scaling `nmul k`
plus a fixed constant `d`. That predicate closes application, `K`, the
higher-type diagonal of `S`, and the base combinators, but it provably cannot
close the recursor `Iter`: the recursor's orbit `L (λ k → iter φ a k)` is
bounded (by `PolyAffine.poly-map-orbit-mult`) by `ω^ι[m]` with `m =
max (length ps) (length dφ)`, a polynomial of *degree `m + 1`* — one higher
than any `nmul K ps ⊞ D` (degree `max (length ps) (length D)`). The recursor
**raises the ω-degree**; the affine bound cannot.

The fix pinned by that analysis: bound the result by `⟦ T ps ⟧` for a genuine
polynomial **transformer** `T : Poly → Poly`, not just an affine one. This
module carries that out. `JBpT σ φ ps T` asserts, relative to the common bound
`ps`, that the (ground-plugged) result is `≤ ⟦ T ps ⟧`; the goodness
`JointAffpT σ φ` packages *some* transformer `T` working for every `ps`. Since
`T ps` is always a polynomial, ground extraction still gives `< ε₀` (indeed
`< ω^ω`); but now the recursor's degree-raising bound `T ps = shift (m+1)
[1]` (denoting `ω^ι[m+1]`) is expressible, so `Iter` closes for an affine
inner function (`𝔅pT-Iter-affine`).

The combinator closures (`app`, `K`, `S`-higher, base) carry over from
`PolyHereditary` and become *simpler*: an abstract transformer composes by
ordinary function composition (`app`'s reindexing is `T ↦ T ∘ (_⊞ dG)`), with
no `nmul`/`⊞` bookkeeping. What the abstract transformer does *not* retain is
the affine *shape* of the inner function, which `Iter` needs to run
`poly-map-orbit-mult`; so the full hereditary `Iter` combinator (threading the
affine data through `𝔅pT (ι ⇒ ι) g`) still requires an affine-tracking
refinement — the honest remaining step, now isolated to exactly that shape
information.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.PolyTransformer
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ⊕-mono-right ; ⊕-increasing-right ; S-increasing ;
        ω^_ ; ω^-mono ; ω^-double ; maxℕ ; _≤ℕ_ ; ≤ℕ-maxL)
open import Claude.BrouwerOrdinals.Affine fe using (⊕-increasing-left)
open import Claude.BrouwerOrdinals.AffineClosure fe using (x-≤-x⊗)
open import Claude.DialogueTreeHeight.Hereditary fe using (Maj ; GroundType)
open import Claude.BrouwerOrdinals.OmegaPoly fe
open import Claude.DialogueTreeHeight.PolyAffine fe
 using (⊞-[] ; nmul ; S⟦⟧≤ ; SZ≤⟦1⟧ ; ι-mono-ℕ ; poly-map-orbit-mult)

\end{code}

`⟦ p ⟧` is below `⟦ p ⊞ q ⟧` in either argument slot (the commutative upper
bound from `poly-key`).

\begin{code}

poly-≤-⊞-left : (p q : Poly) → ⟦ p ⟧ ≤ ⟦ p ⊞ q ⟧
poly-≤-⊞-left p q = ≤-trans (⊕-increasing-right ⟦ p ⟧ ⟦ q ⟧) (poly-key p q)

poly-≤-⊞-right : (p q : Poly) → ⟦ q ⟧ ≤ ⟦ p ⊞ q ⟧
poly-≤-⊞-right p q = ≤-trans (⊕-increasing-left ⟦ p ⟧ ⟦ q ⟧) (poly-key p q)

\end{code}

The polynomial-transformer joint bound `JBpT σ φ ps T`, relative to a common
polynomial bound `ps` on the ground arguments: the result is `≤ ⟦ T ps ⟧`.
Function-type domains are excluded (`GroundType` has removed them).

\begin{code}

JBpT : (σ : type) → Maj σ → Poly → (Poly → Poly) → 𝓤₀ ̇
JBpT ι              a  ps T = a ≤ ⟦ T ps ⟧
JBpT (ι ⇒ τ)        φ  ps T = (x : 𝓑) → x ≤ ⟦ ps ⟧ → JBpT τ (φ x) ps T
JBpT ((σ ⇒ σ') ⇒ τ) φ  ps T = 𝟘

JointAffpT : (σ : type) → Maj σ → 𝓤₀ ̇
JointAffpT σ φ = Σ T ꞉ (Poly → Poly) , ((ps : Poly) → JBpT σ φ ps T)

\end{code}

The function-argument assignments and the hereditary predicate `𝔅pT`,
mutually recursive on the type, exactly as in `PolyHereditary`.

\begin{code}

mutual

 FunArgs : type → 𝓤₀ ̇
 FunArgs ι              = 𝟙
 FunArgs (ι ⇒ τ)        = FunArgs τ
 FunArgs ((σ ⇒ σ') ⇒ τ) = (Σ g ꞉ Maj (σ ⇒ σ') , 𝔅pT (σ ⇒ σ') g) × FunArgs τ

 plug : (σ : type) → Maj σ → FunArgs σ → Maj (GroundType σ)
 plug ι              a _         = a
 plug (ι ⇒ τ)        φ fa        = λ x → plug τ (φ x) fa
 plug ((σ ⇒ σ') ⇒ τ) φ (gg , fa) = plug τ (φ (pr₁ gg)) fa

 𝔅pT : (σ : type) → Maj σ → 𝓤₀ ̇
 𝔅pT σ φ = (fa : FunArgs σ) → JointAffpT (GroundType σ) (plug σ φ fa)

\end{code}

Ground extraction. At type `ι`, `𝔅pT` gives a polynomial bound (evaluate the
transformer at the empty common bound `[]`), hence `< ε₀`.

\begin{code}

𝔅pTι-poly-bound : (a : 𝓑) → 𝔅pT ι a → Σ da ꞉ Poly , a ≤ ⟦ da ⟧
𝔅pTι-poly-bound a good = h (good ⋆)
 where
  h : JointAffpT ι a → Σ da ꞉ Poly , a ≤ ⟦ da ⟧
  h (T , bnd) = T [] , bnd []

𝔅pTι-to-<ε₀ : (a : 𝓑) → 𝔅pT ι a → a < ε₀
𝔅pTι-to-<ε₀ a good with 𝔅pTι-poly-bound a good
... | (da , a≤da) = ≤-trans (≤-S a≤da) (poly-<-ε₀ da)

poly-bounded-to-𝔅pTι : (a : 𝓑) (pa : Poly) → a ≤ ⟦ pa ⟧ → 𝔅pT ι a
poly-bounded-to-𝔅pTι a pa a≤ _ = (λ _ → pa) , (λ ps → a≤)

\end{code}

The application reindexing lemma. When a ground argument `G ≤ ⟦ dG ⟧` is fed
under the enlarged common bound `ps ⊞ dG`, the result — a function of the
*remaining* ground arguments — is recovered at the smaller common bound `ps`
by precomposing the transformer with `_⊞ dG`. This replaces
`PolyHereditary.JBp-shift` and is where the abstract transformer earns its
keep: the reindexing is plain function precomposition, no `nmul` arithmetic.

\begin{code}

JBpT-app-reindex : (σ : type) (φ : Maj σ) (T : Poly → Poly) (dG ps : Poly)
                 → JBpT σ φ (ps ⊞ dG) T → JBpT σ φ ps (λ q → T (q ⊞ dG))
JBpT-app-reindex ι              a T dG ps h = h
JBpT-app-reindex (ι ⇒ τ)        φ T dG ps h =
 λ x x≤ps → JBpT-app-reindex τ (φ x) T dG ps
              (h x (≤-trans x≤ps (poly-≤-⊞-left ps dG)))
JBpT-app-reindex ((σ ⇒ σ') ⇒ τ) φ T dG ps h = h

\end{code}

Application closure. A function argument is threaded through `FunArgs`; a
ground argument `G` is polynomially bounded (`𝔅pTι-poly-bound`), fed to the
transformer under the enlarged common bound `ps ⊞ dG`, then reindexed back to
`ps` by precomposition.

\begin{code}

𝔅pT-app : (σ τ : type) (F : Maj (σ ⇒ τ)) (G : Maj σ)
        → 𝔅pT (σ ⇒ τ) F → 𝔅pT σ G → 𝔅pT τ (F G)
𝔅pT-app (σ ⇒ σ') τ F G hF hG fa = hF ((G , hG) , fa)
𝔅pT-app ι         τ F G hF hG fa with hF fa | 𝔅pTι-poly-bound G hG
... | (T , jbnd) | (dG , G≤dG) =
 (λ q → T (q ⊞ dG)) ,
 (λ ps → JBpT-app-reindex (GroundType τ) (plug τ (F G) fa) T dG ps
           (jbnd (ps ⊞ dG) G (≤-trans G≤dG (poly-≤-⊞-right ps dG))))

\end{code}

The base combinators. `Zero` is the constant `[]`; `Succ` (identity) is the
identity transformer; `Ω` (`λ a → S a`) is `_⊞ [ 1 ]`.

\begin{code}

𝔅pT-Zero : 𝔅pT ι Z
𝔅pT-Zero = poly-bounded-to-𝔅pTι Z [] ≤-Z

𝔅pT-Succ : 𝔅pT (ι ⇒ ι) (λ a → a)
𝔅pT-Succ _ = (λ ps → ps) , (λ ps x x≤ → x≤)

𝔅pT-Ω : 𝔅pT (ι ⇒ ι) (λ a → S a)
𝔅pT-Ω _ = (λ ps → ps ⊞ (1 ∷ [])) ,
          (λ ps x x≤ → ≤-trans (≤-trans (≤-S x≤) (S⟦⟧≤ ps)) (poly-key ps (1 ∷ [])))

\end{code}

Weakening: prefixing an *ignored* argument of any type preserves goodness.

\begin{code}

𝔅pT-weaken : (τ σ : type) (φ : Maj σ) → 𝔅pT σ φ → 𝔅pT (τ ⇒ σ) (λ _ → φ)
𝔅pT-weaken ι         σ φ hφ fa with hφ fa
... | (T , bnd) = T , (λ ps y _ → bnd ps)
𝔅pT-weaken (τ₁ ⇒ τ₂) σ φ hφ ((h , hh) , fa'') = hφ fa''

\end{code}

The `K` combinator, `λ a b → a`. As in `PolyHereditary`: project the first
argument (ground: identity transformer; function: weakening).

\begin{code}

𝔅pT-K : {σ τ : type} → 𝔅pT (σ ⇒ τ ⇒ σ) (λ a b → a)
𝔅pT-K {ι}       {ι}       _                = (λ ps → ps) , (λ ps x x≤ y _ → x≤)
𝔅pT-K {ι}       {τ₁ ⇒ τ₂} ((h , hh) , _)   = (λ ps → ps) , (λ ps x x≤ → x≤)
𝔅pT-K {σ₁ ⇒ σ₂} {τ}       ((g , hg) , fa') = 𝔅pT-weaken τ (σ₁ ⇒ σ₂) g hg fa'

\end{code}

The higher-type diagonal of `S`: `λ a → φ a (γ a)` when the shared argument
`a` has *function* type is a `FunArgs` entry, so the same good majorant `g`
feeds both `φ` and `γ`; the diagonal closes by three applications.

\begin{code}

𝔅pT-S-higher : {ρ₁ ρ₂ σ τ : type}
               (φ : Maj ((ρ₁ ⇒ ρ₂) ⇒ σ ⇒ τ)) (γ : Maj ((ρ₁ ⇒ ρ₂) ⇒ σ))
             → 𝔅pT ((ρ₁ ⇒ ρ₂) ⇒ σ ⇒ τ) φ → 𝔅pT ((ρ₁ ⇒ ρ₂) ⇒ σ) γ
             → 𝔅pT ((ρ₁ ⇒ ρ₂) ⇒ τ) (λ a → φ a (γ a))
𝔅pT-S-higher {ρ₁} {ρ₂} {σ} {τ} φ γ hφ hγ ((g , hg) , fa'') =
 𝔅pT-app σ τ (φ g) (γ g)
   (𝔅pT-app (ρ₁ ⇒ ρ₂) (σ ⇒ τ) φ g hφ hg)
   (𝔅pT-app (ρ₁ ⇒ ρ₂) σ γ g hγ hg)
   fu
 where
  fu : FunArgs τ
  fu = fa''

\end{code}

The recursor, the new content. The ground iteration majorant is
`μ-Iter g a ν = L (λ k → iter g a k) ⊕ ν`. If the inner function `g` is
*affine* — `g b ≤ ⟦ nmul kg pb ⊞ dg ⟧` for `b ≤ ⟦ pb ⟧`, the hypothesis of
`poly-map-orbit-mult` — then the orbit is bounded by `ω^ι[m]` with `m =
max (length ps) (length dg)`, so the majorant is bounded by
`ω^ι[m] ⊕ ω^ι[m] ≤ ω^ι[m] ⊗ ω = ω^ι[m+1] = ⟦ shift (m+1) [1] ⟧`. This is the
degree-raising transformer `T ps = shift (max (length ps) (length dg) + 1)
[1]` — expressible here, impossible in the affine `PolyHereditary.JBp`.

\begin{code}

μ-Iter : (𝓑 → 𝓑) → 𝓑 → 𝓑 → 𝓑
μ-Iter g a ν = L (λ k → iter g a k) ⊕ ν

ω^ι-≤-poly : (m : ℕ) → ω^ ι[ m ] ≤ ⟦ shift m (1 ∷ []) ⟧
ω^ι-≤-poly m =
 transport (ω^ ι[ m ] ≤_) ((shift-pow m (1 ∷ [])) ⁻¹)
           (x-≤-x⊗ (ω^ ι[ m ]) ⟦ 1 ∷ [] ⟧ SZ≤⟦1⟧)

poly-≤-ω^ : (ps : Poly) (m : ℕ) → length ps ≤ℕ m → ⟦ ps ⟧ ≤ ω^ ι[ m ]
poly-≤-ω^ ps m le =
 ≤-trans (S-increasing ⟦ ps ⟧)
   (≤-trans (poly-str ps) (ω^-mono (ι-mono-ℕ (length ps) m le)))

𝔅pT-Iter-affine : (g : 𝓑 → 𝓑) (kg : ℕ) (dg : Poly)
                → ((b : 𝓑) (pb : Poly) → b ≤ ⟦ pb ⟧ → g b ≤ ⟦ nmul kg pb ⊞ dg ⟧)
                → JointAffpT (ι ⇒ ι ⇒ ι) (μ-Iter g)
𝔅pT-Iter-affine g kg dg hg =
 (λ ps → shift (succ (maxℕ (length ps) (length dg))) (1 ∷ [])) , bound
 where
  bound : (ps : Poly) → JBpT (ι ⇒ ι ⇒ ι) (μ-Iter g) ps
                          (λ q → shift (succ (maxℕ (length q) (length dg))) (1 ∷ []))
  bound ps a a≤ ν ν≤ = final
   where
    m : ℕ
    m = maxℕ (length ps) (length dg)

    orbit≤ : L (λ k → iter g a k) ≤ ω^ ι[ m ]
    orbit≤ = poly-map-orbit-mult g kg dg hg a ps a≤

    ν≤ωm : ν ≤ ω^ ι[ m ]
    ν≤ωm = ≤-trans ν≤ (poly-≤-ω^ ps m (≤ℕ-maxL (length ps) (length dg)))

    sum≤ : (L (λ k → iter g a k) ⊕ ν) ≤ (ω^ ι[ m ] ⊕ ω^ ι[ m ])
    sum≤ = ≤-trans (⊕-mono-left orbit≤ ν) (⊕-mono-right (ω^ ι[ m ]) ν≤ωm)

    final : (L (λ k → iter g a k) ⊕ ν) ≤ ⟦ shift (succ m) (1 ∷ []) ⟧
    final = ≤-trans sum≤ (≤-trans (ω^-double ι[ m ]) (ω^ι-≤-poly (succ m)))

\end{code}

`𝔅pT-Iter-affine` closes the recursor for an inner function given with its
affine data. The full hereditary `Iter` combinator would take `g` with only
`𝔅pT (ι ⇒ ι) g` — an *abstract* transformer, which does not expose the affine
shape (`kg , dg`) that `poly-map-orbit-mult` consumes. Recovering it is the
remaining step: an affine-tracking transformer class (coefficient-scaling plus
constant, closed under composition, `⊞`, and the orbit degree-raise), i.e.
Howard's hereditarily-majorizable functionals with a transformer component
that retains enough shape to be iterated. The closures above (`app`, `K`,
`S`-higher, base) and this `Iter` bound show both sides of that class; the
join of the two — abstract-transformer flexibility *plus* affine iterability —
is the honest open interface.

\end{code}
