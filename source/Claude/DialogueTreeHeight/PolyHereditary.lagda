Hereditary poly-affine majorizability (constructive) — the ⊞-based predicate.

The finite-`ι[m]`-multiplier hereditary predicate (`Hereditary`) resolved the
joint/transformer tension, but its affine bound `(s ⊕ d) ⊗ ι[m]` uses the
*non-commutative* ordinal `⊕`/`⊗`, so it cannot reorder or freely duplicate
ground arguments — and it does not carry the multiplicity a combinator like
`S` needs (it feeds its ground argument to its function argument, using it
*twice*). This module rebuilds the predicate over **ω-polynomials** with the
**commutative natural sum** `⊞` and an explicit **multiplicity** `k`:

  `JBp ι a ps k d  =  a ≤ ⟦ nmul k ps ⊞ d ⟧`,

i.e. relative to a common polynomial bound `ps` on all ground arguments, the
result is bounded by `k` copies of `ps` (natural-summed) plus a constant
polynomial `d`. Using `⊞` (commutative, `poly-key` in either order) lets the
combinator proofs reorder and duplicate arguments freely; the multiplicity
`k` is scaled by `nmul` (which grows *coefficients*, not *degree*), so the
recursor orbit stays polynomially bounded (`poly-map-orbit-mult`).

Ground extraction is now `𝔅p ι a ⟺ a is polynomially bounded` (equivalently
`< ω^ω`), *not* `a < ε₀`: the polynomial multiplier caps the fragment at
`ω^ω`. This is the honest ceiling of the ω-polynomial route (see the ceiling
finding in the project notes); the tower to `ε₀` needs `ω^c` (CNF)
multipliers, a separate development. What this module establishes is the
hereditary fundamental theorem *for that maximal polynomial fragment*.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.PolyHereditary
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe using (ι[_] ; ω ; _⊗_)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ⊕-increasing-right)
open import Claude.BrouwerOrdinals.Affine fe using (⊕-increasing-left)
open import Claude.DialogueTreeHeight.Hereditary fe using (Maj ; GroundType)
open import Claude.BrouwerOrdinals.OmegaPoly fe
open import Claude.DialogueTreeHeight.PolyAffine fe
 using (⊞-[] ; ⊞-assoc ; nmul ; S⟦⟧≤)

\end{code}

Some polynomial algebra the predicate needs: the middle-four exchange for the
commutative monoid `(Poly , ⊞ , [])`, distribution of the multiplicity `nmul`
over `⊞`, and `nmul k [] ＝ []`.

\begin{code}

⊞-exch : (a b c d : Poly) → ((a ⊞ b) ⊞ (c ⊞ d)) ＝ ((a ⊞ c) ⊞ (b ⊞ d))
⊞-exch a b c d =
   ⊞-assoc a b (c ⊞ d)
 ∙ ap (a ⊞_) ((⊞-assoc b c d) ⁻¹
             ∙ ap (_⊞ d) (⊞-comm b c)
             ∙ ⊞-assoc c b d)
 ∙ (⊞-assoc a c (b ⊞ d)) ⁻¹

nmul-⊞ : (k : ℕ) (p q : Poly) → nmul k (p ⊞ q) ＝ ((nmul k p) ⊞ (nmul k q))
nmul-⊞ zero     p q = refl
nmul-⊞ (succ k) p q =
 ap ((p ⊞ q) ⊞_) (nmul-⊞ k p q) ∙ ⊞-exch p q (nmul k p) (nmul k q)

nmul-[] : (k : ℕ) → nmul k [] ＝ []
nmul-[] zero     = refl
nmul-[] (succ k) = nmul-[] k

\end{code}

`⟦ p ⟧` is below `⟦ p ⊞ q ⟧` in either argument slot (the commutative upper
bound, from `poly-key`).

\begin{code}

poly-≤-⊞-left : (p q : Poly) → ⟦ p ⟧ ≤ ⟦ p ⊞ q ⟧
poly-≤-⊞-left p q = ≤-trans (⊕-increasing-right ⟦ p ⟧ ⟦ q ⟧) (poly-key p q)

poly-≤-⊞-right : (p q : Poly) → ⟦ q ⟧ ≤ ⟦ p ⊞ q ⟧
poly-≤-⊞-right p q = ≤-trans (⊕-increasing-left ⟦ p ⟧ ⟦ q ⟧) (poly-key p q)

\end{code}

The polynomial joint bound `JBp σ φ ps k d`, relative to a common polynomial
bound `ps` on the ground arguments, with multiplicity `k` and constant `d`.
As with `Hereditary.JB`, function-type domains are excluded (`𝟘`) — `GroundType`
has already removed them.

\begin{code}

JBp : (σ : type) → Maj σ → Poly → ℕ → Poly → 𝓤₀ ̇
JBp ι              a  ps k d = a ≤ ⟦ (nmul k ps) ⊞ d ⟧
JBp (ι ⇒ τ)        φ  ps k d = (x : 𝓑) → x ≤ ⟦ ps ⟧ → JBp τ (φ x) ps k d
JBp ((σ ⇒ σ') ⇒ τ) φ  ps k d = 𝟘

JointAffp : (σ : type) → Maj σ → 𝓤₀ ̇
JointAffp σ φ = Σ k ꞉ ℕ , Σ d ꞉ Poly , ((ps : Poly) → JBp σ φ ps k d)

\end{code}

The function-argument assignments and the hereditary predicate `𝔅p`, mutually
recursive on the type, exactly as in `Hereditary` but over the polynomial
joint bound.

\begin{code}

mutual

 FunArgs : type → 𝓤₀ ̇
 FunArgs ι              = 𝟙
 FunArgs (ι ⇒ τ)        = FunArgs τ
 FunArgs ((σ ⇒ σ') ⇒ τ) = (Σ g ꞉ Maj (σ ⇒ σ') , 𝔅p (σ ⇒ σ') g) × FunArgs τ

 plug : (σ : type) → Maj σ → FunArgs σ → Maj (GroundType σ)
 plug ι              a _         = a
 plug (ι ⇒ τ)        φ fa        = λ x → plug τ (φ x) fa
 plug ((σ ⇒ σ') ⇒ τ) φ (gg , fa) = plug τ (φ (pr₁ gg)) fa

 𝔅p : (σ : type) → Maj σ → 𝓤₀ ̇
 𝔅p σ φ = (fa : FunArgs σ) → JointAffp (GroundType σ) (plug σ φ fa)

\end{code}

Ground extraction. At type `ι`, `𝔅p` is exactly polynomial-boundedness. In
particular a ground majorant is `< ε₀` (indeed `< ω^ω`, being a polynomial).
Instantiating the common bound at `[]` collapses the multiplicity, leaving the
constant polynomial `d`.

\begin{code}

𝔅pι-poly-bound : (a : 𝓑) → 𝔅p ι a → Σ da ꞉ Poly , a ≤ ⟦ da ⟧
𝔅pι-poly-bound a good = h (good ⋆)
 where
  h : JointAffp ι a → Σ da ꞉ Poly , a ≤ ⟦ da ⟧
  h (k , d , bnd) =
   d , transport (λ z → a ≤ ⟦ z ⟧) (ap (_⊞ d) (nmul-[] k)) (bnd [])

𝔅pι-to-<ε₀ : (a : 𝓑) → 𝔅p ι a → a < ε₀
𝔅pι-to-<ε₀ a good with 𝔅pι-poly-bound a good
... | (da , a≤da) = ≤-trans (≤-S a≤da) (poly-<-ε₀ da)

poly-bounded-to-𝔅pι : (a : 𝓑) (pa : Poly) → a ≤ ⟦ pa ⟧ → 𝔅p ι a
poly-bounded-to-𝔅pι a pa a≤ _ = 0 , pa , (λ ps → a≤)

\end{code}

The argument-shift lemma: a common bound `ps ⊞ pG` can be lowered to `ps`,
absorbing the dropped part `pG` into the constant with multiplicity — the
constant grows by `nmul k pG`. This is `Hereditary.JB-shift` redone with the
commutative `⊞` and `nmul` (so it works for every multiplicity `k`, not just a
single additive copy).

\begin{code}

JBp-shift : (σ : type) (φ : Maj σ) (ps pG d : Poly) (k : ℕ)
          → JBp σ φ (ps ⊞ pG) k d → JBp σ φ ps k ((nmul k pG) ⊞ d)
JBp-shift ι              a ps pG d k h =
 transport (λ z → a ≤ ⟦ z ⟧)
           (ap (_⊞ d) (nmul-⊞ k ps pG) ∙ ⊞-assoc (nmul k ps) (nmul k pG) d)
           h
JBp-shift (ι ⇒ τ)        φ ps pG d k h =
 λ x x≤ps → JBp-shift τ (φ x) ps pG d k
              (h x (≤-trans x≤ps (poly-≤-⊞-left ps pG)))
JBp-shift ((σ ⇒ σ') ⇒ τ) φ ps pG d k h = h

\end{code}

Application closure. A function argument is threaded through `FunArgs`; a
ground argument `G` is polynomially bounded (`𝔅pι-poly-bound`), so it is fed to
the transformer under the enlarged common bound `ps ⊞ dG` and then absorbed
into the constant via `JBp-shift`.

\begin{code}

𝔅p-app : (σ τ : type) (F : Maj (σ ⇒ τ)) (G : Maj σ)
       → 𝔅p (σ ⇒ τ) F → 𝔅p σ G → 𝔅p τ (F G)
𝔅p-app (σ ⇒ σ') τ F G hF hG fa = hF ((G , hG) , fa)
𝔅p-app ι         τ F G hF hG fa with hF fa | 𝔅pι-poly-bound G hG
... | (k , d , jbnd) | (dG , G≤dG) =
 k , ((nmul k dG) ⊞ d) ,
 (λ ps → JBp-shift (GroundType τ) (plug τ (F G) fa) ps dG d k
           (jbnd (ps ⊞ dG) G (≤-trans G≤dG (poly-≤-⊞-right ps dG))))

\end{code}

The base combinators are good. `Zero` is the constant polynomial `[]`; `Succ`
(the identity majorant) uses its argument once (`k = 1`, `d = []`); the oracle
`Ω` (`λ a → S a`) uses it once and adds one (`k = 1`, `d = [ 1 ]`).

\begin{code}

𝔅p-Zero : 𝔅p ι Z
𝔅p-Zero = poly-bounded-to-𝔅pι Z [] ≤-Z

\end{code}

Projecting a ground argument: with multiplicity `1` and empty constant, the
common bound `ps` itself bounds the result. `nmul 1 ps ⊞ [] = (ps ⊞ []) ⊞ []`
is `ps` up to the right unit `⊞-[]`, so `x ≤ ⟦ps⟧` transports across.

\begin{code}

proj-bound : (x : 𝓑) (ps : Poly) → x ≤ ⟦ ps ⟧ → x ≤ ⟦ (nmul 1 ps) ⊞ [] ⟧
proj-bound x ps x≤ =
 transport (λ z → x ≤ ⟦ z ⟧) ((⊞-[] (ps ⊞ []) ∙ ⊞-[] ps) ⁻¹) x≤

𝔅p-Succ : 𝔅p (ι ⇒ ι) (λ a → a)
𝔅p-Succ _ = 1 , [] , (λ ps x x≤ → proj-bound x ps x≤)

𝔅p-Ω : 𝔅p (ι ⇒ ι) (λ a → S a)
𝔅p-Ω _ = 1 , (1 ∷ []) ,
         (λ ps x x≤ →
           transport (λ z → S x ≤ ⟦ z ⊞ (1 ∷ []) ⟧) ((⊞-[] ps) ⁻¹)
             (≤-trans (≤-S x≤) (≤-trans (S⟦⟧≤ ps) (poly-key ps (1 ∷ [])))))

\end{code}

Weakening: prefixing an *ignored* argument of any type `τ` preserves goodness.
If `τ` is ground the argument is a discardable ground slot (the joint bound
does not depend on it); if `τ` is a function type the argument is a discardable
`FunArgs` entry. This is the essence of the `K` combinator — introduce and
forget an argument.

\begin{code}

𝔅p-weaken : (τ σ : type) (φ : Maj σ) → 𝔅p σ φ → 𝔅p (τ ⇒ σ) (λ _ → φ)
𝔅p-weaken ι         σ φ hφ fa with hφ fa
... | (k , d , bnd) = k , d , (λ ps y _ → bnd ps)
𝔅p-weaken (τ₁ ⇒ τ₂) σ φ hφ ((h , hh) , fa'') = hφ fa''

\end{code}

The `K` combinator, `μ-K = λ a b → a`. When the projected argument `a` is
ground (`σ = ι`), the result is that ground slot, bounded by the common bound
(`proj-bound`), the second argument `b` being discarded. When `a` is a function
argument (`σ` a function type), `K a` is the constant `λ b → a`, whose goodness
is weakening applied to `a`'s goodness.

\begin{code}

𝔅p-K : {σ τ : type} → 𝔅p (σ ⇒ τ ⇒ σ) (λ a b → a)
𝔅p-K {ι}       {ι}       _                = 1 , [] , (λ ps x x≤ y _ → proj-bound x ps x≤)
𝔅p-K {ι}       {τ₁ ⇒ τ₂} ((h , hh) , _)   = 1 , [] , (λ ps x x≤ → proj-bound x ps x≤)
𝔅p-K {σ₁ ⇒ σ₂} {τ}       ((g , hg) , fa') = 𝔅p-weaken τ (σ₁ ⇒ σ₂) g hg fa'

\end{code}

The `S` combinator, `μ-S φ γ a = φ a (γ a)`. Introducing the two function
arguments `φ`, `γ` reduces goodness of `S` to the **diagonal**: goodness of
`λ a → φ a (γ a)` from goodness of `φ` and `γ`. When the shared argument `a`
has a *function* type it is a `FunArgs` entry, so the same good majorant `g`
can be fed to both `φ` and `γ` — the diagonal closes by three applications of
`𝔅p-app` (share `g`, apply `φ g` to `γ g`). This is the higher-type case of
`S`.

\begin{code}

𝔅p-S-higher : {ρ₁ ρ₂ σ τ : type}
              (φ : Maj ((ρ₁ ⇒ ρ₂) ⇒ σ ⇒ τ)) (γ : Maj ((ρ₁ ⇒ ρ₂) ⇒ σ))
            → 𝔅p ((ρ₁ ⇒ ρ₂) ⇒ σ ⇒ τ) φ → 𝔅p ((ρ₁ ⇒ ρ₂) ⇒ σ) γ
            → 𝔅p ((ρ₁ ⇒ ρ₂) ⇒ τ) (λ a → φ a (γ a))
𝔅p-S-higher {ρ₁} {ρ₂} {σ} {τ} φ γ hφ hγ ((g , hg) , fa'') =
 𝔅p-app σ τ (φ g) (γ g)
   (𝔅p-app (ρ₁ ⇒ ρ₂) (σ ⇒ τ) φ g hφ hg)
   (𝔅p-app (ρ₁ ⇒ ρ₂) σ γ g hγ hg)
   fa''

\end{code}

The two remaining combinator cases — the *ground* diagonal of `S`
(`ρ = ι`, `σ` a function type) and the recursor `𝔅p-Iter` — both fail with the
present `JBp` shape, and for the *same* reason: the joint bound
`a ≤ ⟦ nmul k ps ⊞ d ⟧` is **affine in the common bound `ps`** (coefficient
scaling by `nmul k`, plus a *fixed* constant `d`), and neither operation is
affine in `ps`.

* **Ground `S` (`λ x → φ x (γ x)`, `σ = σ₁ ⇒ σ₂`).** The second argument fed to
  `φ` is `γ x`, a *function-valued* majorant depending on the ground variable
  `x`. But `𝔅p (ι ⇒ (σ₁ ⇒ σ₂) ⇒ τ) φ` fixes `φ`'s function argument as a
  *single* good majorant `g : Maj (σ₁ ⇒ σ₂)`, chosen *before* the ground `x` is
  quantified — so it cannot be `γ x` (which varies with `x`). `𝔅p` records
  function arguments as *fixed* good majorants, whereas `S` needs a
  *ground-context-dependent transformer*. (When `σ = ι` the argument `γ x` is
  ground and this case does close, via multiplicity arithmetic — `nmul`
  distributing over `nmul`/`⊞` — but it is subsumed by the generalisation
  below, so it is not developed here.)

* **`𝔅p-Iter`.** After plugging `φ`, the recursor majorant is
  `λ a ν → L (λ k → iter φ a k) ⊕ ν`. From `hφ` one gets exactly the hypothesis
  of `PolyAffine.poly-map-orbit-mult`, so `L (λ k → iter φ a k) ≤ ω^ι[m]` with
  `m = max (length ps) (length dφ)` when `a ≤ ⟦ ps ⟧`. But `ω^ι[m] =
  ⟦ shift m (1 ∷ []) ⟧` has *degree* `m + 1`, whereas `⟦ nmul K ps ⊞ D ⟧` has
  degree `max (length ps) (length D)`. For a common bound `ps` of unbounded
  degree the recursor's `+1` degree bump exceeds *any fixed* `K, D` — the
  recursor is not affine in `ps`, it *raises the ω-degree*. This is the
  first-order tower (`ω, ω², …`) hitting the affine ceiling.

Both point to the *same* generalisation: `JBp` must bound the result by
`⟦ T ps ⟧` for a **polynomial transformer** `T : Poly → Poly` (closed under
`nmul`, `⊞`, `shift`, and the orbit degree-raise), and `FunArgs` must carry
*transformer-valued* goodness rather than a fixed good majorant. That is
Howard's hereditarily-majorizable functionals with a genuine transformer
component — the substantial redesign the project notes flag, now pinned to a
single precise requirement by the closure of `K`, `S`-higher, `app`, and the
base combinators above.

