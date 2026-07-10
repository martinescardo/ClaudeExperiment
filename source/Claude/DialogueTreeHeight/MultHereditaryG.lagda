Design G, the ground layer: Howard-style data maps over the Design-F
transformers — the transformer tower's first storey.

Every fragment on the Design-F line (`MultHereditaryFT`/`FJT`/`FNT`) carries
*fixed* affine data at ground-domain positions and nothing at function-typed
positions, and the fragment lattice's frontier is exactly where fixed data
fails: a diagonal whose bound must *depend on a function argument's own
bound*. The tower move mirrors Design F one level up: just as `MultHereditaryF`
gave every argument its own globally-valid weight-transformer, here every
argument carries its own **data** — at ground a good bound function, at arrow
types a *map of data*:

  `𝔻 ι = GFun` (a `GoodT` bound function — ground transformers are their own
  data, `selfD`), `𝔻 (σ ⇒ τ) = 𝔻 σ → 𝔻 τ`,

with `BndD` the pointwise bound relation, Howard's majorizability shape. The
payoff of the shape alone is that the *structural* half of the tower is free:

* **`BndD-S` closes for ALL `ρ , σ , τ` in one line** — the diagonal's data
  is the application `(dφ da) (dγ da)`; no zone absorption, no arity ladder,
  no instance families. Likewise `BndD-K`, and application is literal.
  The entire instance-splitting of modules (40)/(42)/(44) was an artifact of
  fixed data.

The residual concentrates in the recursor, exactly as the weight-level
`orbit-good` did in `MultHereditaryF`: the recursor's data must be the
*orbit of the argument's data map*, and for an arbitrary map that orbit is
unbounded — `λ b → ω^ ∘ b`-style maps are legal `𝔻 (ι ⇒ ι)`, mirroring the
`ω^` counterexample one level up. The maps a term denotes are however
**tracked**: dominated by an inner-affine bound-transformer. `Tracked F`
packages that domination, and the point of this module is that the *entire*
affine calculus of `MultHereditaryFAff` transfers along it:

* `Tracked-∘` is `AffBounded-∘` applied to the dominating transformers;
* **`BndD-orbit`** — the engine: for a tracked `dg`, the recursor's data
  orbit is bounded, via `aff-orbit-≤` on the dominating transformer, giving
  `dOrbit` (a bona fide `𝔻 ι → 𝔻 ι`) with `Tracked-dOrbit` (the orbit map is
  itself tracked, multiplier raised one `ω`-exponent — so nested recursion
  stays tracked); `BndD-Iter` assembles the recursor's closure.

Honest scope — what a fundamental theorem still needs: `Tracked` must be
carried *hereditarily* (a type-indexed tracking relation `𝕂`, with tracked
maps of tracked maps), so that `Iter`'s hypothesis is supplied
compositionally rather than taken as an argument; its `K`/`S` closure is the
zone calculus of (39)–(44) replayed at the data level (the two-argument
tracked diagonal is an `Aff₂`-shape on bound functions, and so on up —
the same arithmetic, one level up, all of it already proven at level one
here by reuse). That assembly — Howard's hereditarily-majorizable
functionals with affine tracking — is the pinned next development. The
conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryG
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
 using (_<_ ; ε₀ ; ω^_ ; S-<-ε₀ ; ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right ;
        ⊕-increasing-right ; ⊕-<-ε₀ ; ω^-<-ε₀ ; tower-<-ε₀)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊕-increasing-left)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (⊗-<-ε₀)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (x-≤-x⊗ ; Z<ε₀ ; ι<ε₀)
open import Claude.BrouwerOrdinals.MultAffine fe using (ω-pos)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; ω-valid ; validMult-⊗ ; validMult-orbit)
open import Claude.DialogueTreeHeight.MultHereditaryF fe
 using (𝕋 ; GoodT ; Torbit ; GoodT-⊕)
open import Claude.DialogueTreeHeight.MultHereditaryFAff fe
 using (AffBounded ; AffBounded-∘ ; aff-orbit-≤)

\end{code}

The data hierarchy and the bound relation. At ground, data is a good bound
function and a ground transformer is its own data.

\begin{code}

GFun : 𝓤₀ ̇
GFun = Σ B ꞉ (𝓑 → 𝓑) , GoodT ι B

𝔻 : type → 𝓤₀ ̇
𝔻 ι       = GFun
𝔻 (σ ⇒ τ) = 𝔻 σ → 𝔻 τ

BndD : (τ : type) → 𝕋 τ → 𝔻 τ → 𝓤₀ ̇
BndD ι       a d = (w : 𝓑) → a w ≤ pr₁ d w
BndD (σ ⇒ τ) T F = (g : 𝕋 σ) (dg : 𝔻 σ) → BndD σ g dg → BndD τ (T g) (F dg)

selfD : (T : 𝕋 ι) → GoodT ι T → 𝔻 ι
selfD T gT = T , gT

selfD-bnd : (T : 𝕋 ι) (gT : GoodT ι T) → BndD ι T (selfD T gT)
selfD-bnd T gT = λ w → ≤-refl (T w)

\end{code}

The structural half of the tower, free of charge: `K` and — for all
`ρ , σ , τ` at once, with no instance families and no zone arithmetic —
the full `S`, whose diagonal data is application. Application itself is
literal (`BndD (σ ⇒ τ)` *is* the application clause). The base combinators'
transformers: `Succ ↦` the identity map, `Ω ↦` pointwise successor.

\begin{code}

BndD-K : {σ τ : type}
       → BndD (σ ⇒ τ ⇒ σ) (λ Ta Tb → Ta) (λ da db → da)
BndD-K = λ a da ba b db bb → ba

BndD-S : {ρ σ τ : type}
       → BndD ((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ)
              (λ Tφ Tγ Ta → (Tφ Ta) (Tγ Ta))
              (λ dφ dγ da → (dφ da) (dγ da))
BndD-S = λ φ dφ bφ γ dγ bγ a da ba →
          bφ a da ba (γ a) (dγ da) (bγ a da ba)

BndD-Succ : BndD (ι ⇒ ι) (λ Tg → Tg) (λ d → d)
BndD-Succ = λ g dg bg → bg

dΩ : 𝔻 (ι ⇒ ι)
dΩ d = (λ w → S (pr₁ d w))
     , (λ w p → S-<-ε₀ (pr₁ d w) (pr₁ (pr₂ d) w p))
     , (λ w w′ q → ≤-S (pr₂ (pr₂ d) w w′ q))

BndD-Ω : BndD (ι ⇒ ι) (λ Tg w → S (Tg w)) dΩ
BndD-Ω = λ g dg bg w → ≤-S (bg w)

\end{code}

Tracking. A data map is tracked if it is dominated by an inner-affine
bound-transformer — the `AffBounded` shape of `MultHereditaryFAff`, read on
bound functions. The dominating transformer `Taff D c M` is affinely bounded
by construction and monotone, which is what lets the affine calculus
transfer.

\begin{code}

Tracked : (𝔻 ι → 𝔻 ι) → 𝓤₀ ̇
Tracked F = Σ D ꞉ (𝓑 → 𝓑) , Σ c ꞉ 𝓑 , Σ M ꞉ 𝓑 ,
               GoodT ι D × (c < ε₀) × ValidMult M
             × ((b : 𝔻 ι) (w : 𝓑)
                  → pr₁ (F b) w ≤ ((D w ⊕ (pr₁ b w ⊕ c)) ⊗ M))

Taff : (𝓑 → 𝓑) → 𝓑 → 𝓑 → 𝕋 (ι ⇒ ι)
Taff D c M = λ T w → ((D w ⊕ (T w ⊕ c)) ⊗ M)

Taff-mono : (D : 𝓑 → 𝓑) (c M : 𝓑) (T T′ : 𝓑 → 𝓑)
          → ((w : 𝓑) → T w ≤ T′ w)
          → (w : 𝓑) → Taff D c M T w ≤ Taff D c M T′ w
Taff-mono D c M T T′ h w =
 ⊗-mono-left (⊕-mono-right (D w) (⊕-mono-left (h w) c)) M

Taff-aff : (D : 𝓑 → 𝓑) (c M : 𝓑)
         → GoodT ι D → c < ε₀ → ValidMult M
         → AffBounded (Taff D c M)
Taff-aff D c M gD cε vM = D , c , M , gD , cε , vM , (λ T w → ≤-refl _)

\end{code}

The tracked maps a term's combinators denote: identity (`Succ`), constants
(`K`), pointwise successor (`Ω`), and — the composition closure, by direct
reuse of `AffBounded-∘` on the dominating transformers — composites.

\begin{code}

Tracked-id : Tracked (λ b → b)
Tracked-id = (λ _ → Z) , Z , ω
 , ((λ w _ → Z<ε₀) , (λ w w′ _ → ≤-Z)) , Z<ε₀ , ω-valid
 , (λ b w → ≤-trans (⊕-increasing-left Z (pr₁ b w))
                    (x-≤-x⊗ (Z ⊕ pr₁ b w) ω ω-pos))

Tracked-const : (t : 𝔻 ι) → Tracked (λ _ → t)
Tracked-const t = pr₁ t , Z , ω , pr₂ t , Z<ε₀ , ω-valid
 , (λ b w → ≤-trans (⊕-increasing-right (pr₁ t w) (pr₁ b w))
                    (x-≤-x⊗ (pr₁ t w ⊕ pr₁ b w) ω ω-pos))

Tracked-dΩ : Tracked dΩ
Tracked-dΩ = (λ _ → Z) , ι[ 1 ] , ω
 , ((λ w _ → Z<ε₀) , (λ w w′ _ → ≤-Z)) , ι<ε₀ 1 , ω-valid
 , (λ b w → ≤-trans (⊕-increasing-left Z (S (pr₁ b w)))
                    (x-≤-x⊗ (Z ⊕ S (pr₁ b w)) ω ω-pos))

Tracked-∘ : (F G : 𝔻 ι → 𝔻 ι) → Tracked F → Tracked G
          → Tracked (λ b → F (G b))
Tracked-∘ F G (DF , cF , MF , gDF , cFε , vMF , tF)
              (DG , cG , MG , gDG , cGε , vMG , tG) =
 finish (AffBounded-∘ (Taff DF cF MF) (Taff DG cG MG)
          (Taff-aff DF cF MF gDF cFε vMF)
          (Taff-aff DG cG MG gDG cGε vMG))
 where
  finish : AffBounded (λ T → Taff DF cF MF (Taff DG cG MG T))
         → Tracked (λ b → F (G b))
  finish (D★ , c★ , M★ , gD★ , c★ε , vM★ , b★) =
   D★ , c★ , M★ , gD★ , c★ε , vM★ , bound
   where
    bound : (b : 𝔻 ι) (w : 𝓑)
          → pr₁ (F (G b)) w ≤ ((D★ w ⊕ (pr₁ b w ⊕ c★)) ⊗ M★)
    bound b w =
     ≤-trans (tF (G b) w)
      (≤-trans (Taff-mono DF cF MF (pr₁ (G b))
                 (Taff DG cG MG (pr₁ b)) (tG b) w)
               (b★ (pr₁ b) w))

\end{code}

The data-level orbit engine — the recursor's storey. For a tracked `dg`,
iterating the data map from `da` is dominated, bound-functionwise, by
iterating the dominating transformer, so `aff-orbit-≤` bounds the orbit:
`dOrbit dg trk da` is a genuine `𝔻 ι`, `BndD-orbit` says it bounds the
transformer orbit `Torbit`, and `Tracked-dOrbit` says the orbit map is
itself tracked at the multiplier raised one `ω`-exponent — so nested
recursion stays inside the tracked class, one exponent per nesting level,
exactly as in `AffBounded-orbit`.

\begin{code}

dOrbit : (F : 𝔻 ι → 𝔻 ι) → Tracked F → 𝔻 ι → 𝔻 ι
dOrbit F (D , c , M , (Dpres , Dmono) , cε , vM , tb) (B , Bpres , Bmono) =
 (λ w → ((D w ⊕ B w) ⊕ c) ⊗ ω^ ((ω ⊗ M) ⊗ ω))
 , (λ w p → ⊗-<-ε₀ ((D w ⊕ B w) ⊕ c) (ω^ ((ω ⊗ M) ⊗ ω))
             (⊕-<-ε₀ (D w ⊕ B w) c
               (⊕-<-ε₀ (D w) (B w) (Dpres w p) (Bpres w p)) cε)
             (ω^-<-ε₀ ((ω ⊗ M) ⊗ ω)
               (⊗-<-ε₀ (ω ⊗ M) ω
                 (⊗-<-ε₀ ω M (tower-<-ε₀ 0) (pr₂ (pr₂ vM)))
                 (tower-<-ε₀ 0))))
 , (λ w w′ q → ⊗-mono-left
                (⊕-mono-left
                  (≤-trans (⊕-mono-left (Dmono w w′ q) (B w))
                           (⊕-mono-right (D w′) (Bmono w w′ q)))
                  c)
                (ω^ ((ω ⊗ M) ⊗ ω)))

BndD-orbit : (Tg : 𝕋 (ι ⇒ ι)) (dg : 𝔻 (ι ⇒ ι))
           → BndD (ι ⇒ ι) Tg dg → (trk : Tracked dg)
           → (Ta : 𝕋 ι) (da : 𝔻 ι) → BndD ι Ta da
           → BndD ι (Torbit Tg Ta) (dOrbit dg trk da)
BndD-orbit Tg dg bndg trk@(D , c , M , gD , cε , vM , tb) Ta da ba = goal
 where
  Th : 𝕋 (ι ⇒ ι)
  Th = Taff D c M

  Ba : 𝓑 → 𝓑
  Ba = pr₁ da

  dseq : ℕ → 𝔻 ι
  dseq zero     = da
  dseq (succ k) = dg (dseq k)

  chain₁ : (k : ℕ) → BndD ι (iter Tg Ta k) (dseq k)
  chain₁ zero     = ba
  chain₁ (succ k) = bndg (iter Tg Ta k) (dseq k) (chain₁ k)

  chain₂ : (k : ℕ) (w : 𝓑) → pr₁ (dseq k) w ≤ iter Th Ba k w
  chain₂ zero     w = ≤-refl (Ba w)
  chain₂ (succ k) w =
   ≤-trans (tb (dseq k) w)
           (Taff-mono D c M (pr₁ (dseq k)) (iter Th Ba k) (chain₂ k) w)

  goal : (w : 𝓑) → Torbit Tg Ta w
                   ≤ (((D w ⊕ Ba w) ⊕ c) ⊗ ω^ ((ω ⊗ M) ⊗ ω))
  goal w =
   ≤-trans (≤-L-mono (λ k → ≤-trans (chain₁ k w) (chain₂ k w)))
           (aff-orbit-≤ Th D c M vM (λ T w′ → ≤-refl (Taff D c M T w′)) Ba w)

Tracked-dOrbit : (F : 𝔻 ι → 𝔻 ι) (trk : Tracked F) → Tracked (dOrbit F trk)
Tracked-dOrbit F trk@(D , c , M , gD , cε , vM , tb) =
 D , c , ω^ ((ω ⊗ M) ⊗ ω) , gD , cε
 , validMult-orbit (validMult-⊗ ω-valid vM)
 , bound
 where
  bound : (b : 𝔻 ι) (w : 𝓑)
        → pr₁ (dOrbit F trk b) w
          ≤ ((D w ⊕ (pr₁ b w ⊕ c)) ⊗ ω^ ((ω ⊗ M) ⊗ ω))
  bound b w =
   transport (λ z → pr₁ (dOrbit F trk b) w ≤ (z ⊗ ω^ ((ω ⊗ M) ⊗ ω)))
             (⊕-assoc (D w) (pr₁ b w) c)
             (≤-refl (((D w ⊕ pr₁ b w) ⊕ c) ⊗ ω^ ((ω ⊗ M) ⊗ ω)))

\end{code}

The recursor's closure, assembled: given a tracked data map for the iterated
argument, the recursor's transformer is bounded by the orbit data plus the
count.

\begin{code}

dsum : 𝔻 ι → 𝔻 ι → 𝔻 ι
dsum (B₁ , g₁) (B₂ , g₂) = (λ w → B₁ w ⊕ B₂ w) , GoodT-⊕ B₁ B₂ g₁ g₂

BndD-Iter : (Tg : 𝕋 (ι ⇒ ι)) (dg : 𝔻 (ι ⇒ ι))
          → BndD (ι ⇒ ι) Tg dg → (trk : Tracked dg)
          → BndD (ι ⇒ ι ⇒ ι)
                 (λ Ta Tν w → Torbit Tg Ta w ⊕ Tν w)
                 (λ da dν → dsum (dOrbit dg trk da) dν)
BndD-Iter Tg dg bndg trk = λ Ta da ba Tν dν bν w →
 ≤-trans (⊕-mono-left (BndD-orbit Tg dg bndg trk Ta da ba w) (Tν w))
         (⊕-mono-right (pr₁ (dOrbit dg trk da) w) (bν w))

\end{code}
