Hereditary CNF-transformer majorizability (constructive) — the `ε₀` lift of
`PolyTransformer`.

`PolyTransformer` built the hereditary predicate over a *polynomial*
transformer `T : Poly → Poly`, closing application, `K`, the higher-type
diagonal of `S`, and the base combinators, with ground extraction landing at
`< ω^ω` (polynomials cap there). This module reruns exactly that development
over **Cantor normal forms** (`CNF`): the transformer is `T : CNF → CNF`, and
ground extraction now lands at **`< ε₀`** (every CNF is `< ε₀`), removing the
`ω^ω` ceiling from the hereditary predicate.

The port is mechanical: the abstract transformer composes by ordinary function
composition, so nothing here needs the commutative natural sum — the ordinary
CNF sum `⊕c` (which only has to be *increasing* on each side, not commutative)
suffices for the application reindexing, exactly as `⊞` did one level down. What
does **not** port is the recursor `Iter` and the *ground* diagonal of `S`
(`PolyTransformer` left both open): they need the transformer to expose enough
shape to be iterated, which the abstract `T` drops. So this establishes the
hereditary fundamental theorem *at `ε₀`* for the same fragment
`PolyTransformer` reached at `ω^ω` — `K`, `S`-higher, application, and the base
combinators — with the arithmetic ceiling gone; the structural residual is
unchanged.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.CNFTransformer
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe
 using (ω ; _⊗_ ; ⊕-mono-left ; orbit-sup-≤)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ⊕-increasing-right ; ⊕-mono-right)
open import Claude.BrouwerOrdinals.Affine fe using (⊕-increasing-left)
open import Claude.DialogueTreeHeight.Hereditary fe using (Maj ; GroundType)
open import Claude.BrouwerOrdinals.CNF fe
open import Claude.BrouwerOrdinals.CNFAffine fe using (scaleω ; scaleω-bound)

\end{code}

`⟦ p ⟧` is below `⟦ p ⊕c q ⟧` in either slot — the ordinary CNF sum is
increasing on both sides (no commutativity needed; that is only for the
multi-argument joint bound elsewhere).

\begin{code}

cnf-≤-⊕c-left : (p q : CNF) → ⟦ p ⟧ ≤ ⟦ p ⊕c q ⟧
cnf-≤-⊕c-left p q =
 transport (⟦ p ⟧ ≤_) ((⊕c-⟦⟧ p q) ⁻¹) (⊕-increasing-right ⟦ p ⟧ ⟦ q ⟧)

cnf-≤-⊕c-right : (p q : CNF) → ⟦ q ⟧ ≤ ⟦ p ⊕c q ⟧
cnf-≤-⊕c-right p q =
 transport (⟦ q ⟧ ≤_) ((⊕c-⟦⟧ p q) ⁻¹) (⊕-increasing-left ⟦ p ⟧ ⟦ q ⟧)

\end{code}

The CNF-transformer joint bound and the goodness predicate — verbatim
`PolyTransformer`, with `Poly ↦ CNF`.

\begin{code}

JBpT : (σ : type) → Maj σ → CNF → (CNF → CNF) → 𝓤₀ ̇
JBpT ι              a  ps T = a ≤ ⟦ T ps ⟧
JBpT (ι ⇒ τ)        φ  ps T = (x : 𝓑) → x ≤ ⟦ ps ⟧ → JBpT τ (φ x) ps T
JBpT ((σ ⇒ σ') ⇒ τ) φ  ps T = 𝟘

JointAffpT : (σ : type) → Maj σ → 𝓤₀ ̇
JointAffpT σ φ = Σ T ꞉ (CNF → CNF) , ((ps : CNF) → JBpT σ φ ps T)

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

Ground extraction — now at `ε₀`. Evaluating the transformer at `𝟎` gives a CNF
bound, hence `< ε₀`.

\begin{code}

𝔅pTι-cnf-bound : (a : 𝓑) → 𝔅pT ι a → Σ da ꞉ CNF , a ≤ ⟦ da ⟧
𝔅pTι-cnf-bound a good = h (good ⋆)
 where
  h : JointAffpT ι a → Σ da ꞉ CNF , a ≤ ⟦ da ⟧
  h (T , bnd) = T 𝟎 , bnd 𝟎

𝔅pTι-to-<ε₀ : (a : 𝓑) → 𝔅pT ι a → a < ε₀
𝔅pTι-to-<ε₀ a good with 𝔅pTι-cnf-bound a good
... | (da , a≤da) = ≤-trans (≤-S a≤da) (cnf-<-ε₀ da)

cnf-bounded-to-𝔅pTι : (a : 𝓑) (pa : CNF) → a ≤ ⟦ pa ⟧ → 𝔅pT ι a
cnf-bounded-to-𝔅pTι a pa a≤ _ = (λ _ → pa) , (λ ps → a≤)

\end{code}

Application reindexing and closure — the abstract transformer is precomposed
with `_⊕c dG`.

\begin{code}

JBpT-app-reindex : (σ : type) (φ : Maj σ) (T : CNF → CNF) (dG ps : CNF)
                 → JBpT σ φ (ps ⊕c dG) T → JBpT σ φ ps (λ q → T (q ⊕c dG))
JBpT-app-reindex ι              a T dG ps h = h
JBpT-app-reindex (ι ⇒ τ)        φ T dG ps h =
 λ x x≤ps → JBpT-app-reindex τ (φ x) T dG ps
              (h x (≤-trans x≤ps (cnf-≤-⊕c-left ps dG)))
JBpT-app-reindex ((σ ⇒ σ') ⇒ τ) φ T dG ps h = h

𝔅pT-app : (σ τ : type) (F : Maj (σ ⇒ τ)) (G : Maj σ)
        → 𝔅pT (σ ⇒ τ) F → 𝔅pT σ G → 𝔅pT τ (F G)
𝔅pT-app (σ ⇒ σ') τ F G hF hG fa = hF ((G , hG) , fa)
𝔅pT-app ι         τ F G hF hG fa with hF fa | 𝔅pTι-cnf-bound G hG
... | (T , jbnd) | (dG , G≤dG) =
 (λ q → T (q ⊕c dG)) ,
 (λ ps → JBpT-app-reindex (GroundType τ) (plug τ (F G) fa) T dG ps
           (jbnd (ps ⊕c dG) G (≤-trans G≤dG (cnf-≤-⊕c-right ps dG))))

\end{code}

The base combinators. `Zero ↦ 𝟎`; `Succ` the identity transformer; `Ω` adds the
CNF `ω⟨ 𝟎 ⟩+ 𝟎` (denoting `1`) on the right.

\begin{code}

𝔅pT-Zero : 𝔅pT ι Z
𝔅pT-Zero = cnf-bounded-to-𝔅pTι Z 𝟎 ≤-Z

𝔅pT-Succ : 𝔅pT (ι ⇒ ι) (λ a → a)
𝔅pT-Succ _ = (λ ps → ps) , (λ ps x x≤ → x≤)

𝔅pT-Ω : 𝔅pT (ι ⇒ ι) (λ a → S a)
𝔅pT-Ω _ = (λ ps → ps ⊕c (ω⟨ 𝟎 ⟩+ 𝟎)) ,
          (λ ps x x≤ →
            transport (S x ≤_) ((⊕c-⟦⟧ ps (ω⟨ 𝟎 ⟩+ 𝟎)) ⁻¹) (≤-S x≤))

\end{code}

Weakening and `K` — identical to `PolyTransformer`.

\begin{code}

𝔅pT-weaken : (τ σ : type) (φ : Maj σ) → 𝔅pT σ φ → 𝔅pT (τ ⇒ σ) (λ _ → φ)
𝔅pT-weaken ι         σ φ hφ fa with hφ fa
... | (T , bnd) = T , (λ ps y _ → bnd ps)
𝔅pT-weaken (τ₁ ⇒ τ₂) σ φ hφ ((h , hh) , fa'') = hφ fa''

𝔅pT-K : {σ τ : type} → 𝔅pT (σ ⇒ τ ⇒ σ) (λ a b → a)
𝔅pT-K {ι}       {ι}       _                = (λ ps → ps) , (λ ps x x≤ y _ → x≤)
𝔅pT-K {ι}       {τ₁ ⇒ τ₂} ((h , hh) , _)   = (λ ps → ps) , (λ ps x x≤ → x≤)
𝔅pT-K {σ₁ ⇒ σ₂} {τ}       ((g , hg) , fa') = 𝔅pT-weaken τ (σ₁ ⇒ σ₂) g hg fa'

\end{code}

The higher-type diagonal of `S` — three applications sharing the same function
argument.

\begin{code}

𝔅pT-S-higher : {ρ₁ ρ₂ σ τ : type}
               (φ : Maj ((ρ₁ ⇒ ρ₂) ⇒ σ ⇒ τ)) (γ : Maj ((ρ₁ ⇒ ρ₂) ⇒ σ))
             → 𝔅pT ((ρ₁ ⇒ ρ₂) ⇒ σ ⇒ τ) φ → 𝔅pT ((ρ₁ ⇒ ρ₂) ⇒ σ) γ
             → 𝔅pT ((ρ₁ ⇒ ρ₂) ⇒ τ) (λ a → φ a (γ a))
𝔅pT-S-higher {ρ₁} {ρ₂} {σ} {τ} φ γ hφ hγ ((g , hg) , fa'') =
 𝔅pT-app σ τ (φ g) (γ g)
   (𝔅pT-app (ρ₁ ⇒ ρ₂) (σ ⇒ τ) φ g hφ hg)
   (𝔅pT-app (ρ₁ ⇒ ρ₂) σ γ g hγ hg)
   fa''

\end{code}

So `K`, `S`-higher, application and the base combinators close the hereditary
CNF-transformer predicate, with ground extraction at `ε₀`.

The recursor, for an **additive** inner function — the new content the CNF
arithmetic unlocks. `PolyTransformer.𝔅pT-Iter-affine` closed `Iter` at `ω^ω`
by producing a *degree-raising* polynomial transformer; here the transformer is
a genuine CNF, so the bound reaches `ε₀`. Given `g` additive with a fixed CNF
increment `c` (`g b ≤ b ⊕ ⟦ c ⟧`), the recursor majorant `μ-Iter g a ν =
L (λ k → iter g a k) ⊕ ν` has orbit `≤ a ⊕ (⟦ c ⟧ ⊗ ω)` (the `Orbit` engine),
and `⟦ c ⟧ ⊗ ω ≤ ⟦ scaleω c ⟧` (`CNFAffine.scaleω`) turns that into the CNF
transformer `T p = (p ⊕c scaleω c) ⊕c p` — bounding start, increment and count.
So the recursor's output is expressible as a CNF transformer at `ε₀`, closing
the `Iter` case for an additive inner function.

\begin{code}

μ-Iter : (𝓑 → 𝓑) → 𝓑 → 𝓑 → 𝓑
μ-Iter g a ν = L (λ k → iter g a k) ⊕ ν

𝔅pT-Iter-additive : (g : 𝓑 → 𝓑) (c : CNF)
                   → ((b : 𝓑) → g b ≤ (b ⊕ ⟦ c ⟧))
                   → JointAffpT (ι ⇒ ι ⇒ ι) (μ-Iter g)
𝔅pT-Iter-additive g c gstep =
 (λ p → (p ⊕c scaleω c) ⊕c p) , bound
 where
  bound : (p : CNF) (a : 𝓑) → a ≤ ⟦ p ⟧ → (ν : 𝓑) → ν ≤ ⟦ p ⟧
        → μ-Iter g a ν ≤ ⟦ (p ⊕c scaleω c) ⊕c p ⟧
  bound p a a≤ ν ν≤ =
   transport (λ z → (L (λ k → iter g a k) ⊕ ν) ≤ z) eq
     (≤-trans (⊕-mono-left orbit ν)
       (≤-trans (⊕-mono-left ap≤ ν)
                (⊕-mono-right (⟦ p ⟧ ⊕ ⟦ scaleω c ⟧) ν≤)))
   where
    step : (k : ℕ) → iter g a (succ k) ≤ (iter g a k ⊕ ⟦ c ⟧)
    step k = gstep (iter g a k)

    orbit : L (λ k → iter g a k) ≤ (a ⊕ (⟦ c ⟧ ⊗ ω))
    orbit = orbit-sup-≤ (iter g a) ⟦ c ⟧ step

    ap≤ : (a ⊕ (⟦ c ⟧ ⊗ ω)) ≤ (⟦ p ⟧ ⊕ ⟦ scaleω c ⟧)
    ap≤ = ≤-trans (⊕-mono-left a≤ (⟦ c ⟧ ⊗ ω))
                  (⊕-mono-right ⟦ p ⟧ (scaleω-bound c))

    eq : ((⟦ p ⟧ ⊕ ⟦ scaleω c ⟧) ⊕ ⟦ p ⟧) ＝ ⟦ (p ⊕c scaleω c) ⊕c p ⟧
    eq = ap (_⊕ ⟦ p ⟧) ((⊕c-⟦⟧ p (scaleω c)) ⁻¹)
       ∙ (⊕c-⟦⟧ (p ⊕c scaleω c) p) ⁻¹

\end{code}

The *ground* diagonal of `S` remains open (the abstract transformer records a
function argument as a single good majorant, not a ground-context-dependent
transformer — `PolyTransformer`'s residual, unchanged), and the fully
hereditary `Iter` combinator still needs `𝔅pT (ι ⇒ ι) g` to expose additive (or
affine) shape rather than an abstract transformer. But the recursor's *output*
is now a genuine `ε₀` CNF transformer, and `K`, `S`-higher, application and the
base combinators close — the hereditary fundamental theorem at `ε₀` for that
fragment, arithmetic ceiling gone.

\end{code}
