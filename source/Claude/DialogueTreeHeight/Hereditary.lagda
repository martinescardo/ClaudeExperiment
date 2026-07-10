Hereditary affine majorizability (constructive) — toward `μ t < ε₀`.

The recursor majorant needs its iterated `ι⇒ι` function to be affine; the
affine-closure toolkit (`AffineClosure`) shows the base `ι⇒ι` majorants are
affine and that affine functions compose. The remaining step is to propagate
affineness *hereditarily* through all (first-order) types — Howard's
hereditarily-majorizable functionals — so that `μ F` is affine for every
first-order `F : ι⇒ι`.

The obstacle is that ground arguments need a *uniform joint* affine bound,
while function arguments need a *data-dependent transformer*. The resolution
here: a majorant `φ : Maj σ` is "good" (`𝔅 σ φ`) iff, for every assignment of
good majorants to the *function* arguments of `σ`, the result — read as a
function of the *ground* arguments of `σ` — is *jointly affine*. The function
arguments are universally quantified (transformer), and the ground arguments
get one uniform affine bound (joint). `plug` performs the substitution of the
function arguments, leaving a first-order (`ι^n⇒ι`) majorant on which the
joint affine bound `JointAff` is asserted.

This module sets up the predicate and the ground extraction; the combinator
cases of the fundamental theorem are developed on top.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.Hereditary
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import EffectfulForcing.MFPSAndVariations.MFPS-XXIX using (B-Set⟦_⟧)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe using (ι[_] ; ω ; _⊗_ ; ⊕-assoc)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; Z-left-unit ; ⊕-increasing-right ; ⊕-<-ε₀)
open import Claude.BrouwerOrdinals.Affine fe using (⊕-increasing-left)
open import Claude.BrouwerOrdinals.AffineClosure fe using (⊗ι-<-ε₀ ; Z<ε₀ ; ι<ε₀)

\end{code}

The majorant type (same as `Majorant.Maj`, repeated to avoid a heavy import).

\begin{code}

Maj : type → 𝓤₀ ̇
Maj ι       = 𝓑
Maj (σ ⇒ τ) = Maj σ → Maj τ

\end{code}

`GroundType σ` keeps only the ground (`ι`-domain) arguments of `σ`; it is
always of the form `ι^n ⇒ ι`. `JB σ φ s d m` is the joint affine bound for
such a first-order majorant, *relative to a common upper bound* `s` on all the
ground arguments: applied to any `x⃗` with each `xᵢ ≤ s`, the result is
`≤ (s ⊕ d) ⊗ ι[m]`. Using one common bound `s` (rather than the ordered sum
of the arguments) makes the bound symmetric in the arguments, so the
combinator proofs reorder/duplicate arguments using only associativity of
`⊕`, never commutativity (which fails for the ordinal sum).

\begin{code}

GroundType : type → type
GroundType ι              = ι
GroundType (ι ⇒ τ)        = ι ⇒ GroundType τ
GroundType ((σ ⇒ σ') ⇒ τ) = GroundType τ

JB : (σ : type) → Maj σ → 𝓑 → 𝓑 → ℕ → 𝓤₀ ̇
JB ι              a s d m = a ≤ ((s ⊕ d) ⊗ ι[ m ])
JB (ι ⇒ τ)        φ s d m = (x : 𝓑) → x ≤ s → JB τ (φ x) s d m
JB ((σ ⇒ σ') ⇒ τ) φ s d m = 𝟘

JointAff : (σ : type) → Maj σ → 𝓤₀ ̇
JointAff σ φ =
 Σ d ꞉ 𝓑 , Σ m ꞉ ℕ , (S Z ≤ ι[ m ]) × (d < ε₀) × ((s : 𝓑) → JB σ φ s d m)

\end{code}

The function-argument assignments of a type, carrying a goodness proof for
each function argument; `plug` substitutes them, leaving a first-order
majorant. The predicate `𝔅` and the assignments `FunArgs` are mutually
recursive on the type.

\begin{code}

mutual

 FunArgs : type → 𝓤₀ ̇
 FunArgs ι              = 𝟙
 FunArgs (ι ⇒ τ)        = FunArgs τ
 FunArgs ((σ ⇒ σ') ⇒ τ) = (Σ g ꞉ Maj (σ ⇒ σ') , 𝔅 (σ ⇒ σ') g) × FunArgs τ

 plug : (σ : type) → Maj σ → FunArgs σ → Maj (GroundType σ)
 plug ι              a _         = a
 plug (ι ⇒ τ)        φ fa        = λ x → plug τ (φ x) fa
 plug ((σ ⇒ σ') ⇒ τ) φ (gg , fa) = plug τ (φ (pr₁ gg)) fa

 𝔅 : (σ : type) → Maj σ → 𝓤₀ ̇
 𝔅 σ φ = (fa : FunArgs σ) → JointAff (GroundType σ) (plug σ φ fa)

\end{code}

Ground extraction: at type `ι`, `𝔅` is equivalent to being `< ε₀`.

\begin{code}

𝔅ι-to-<ε₀ : (a : 𝓑) → 𝔅 ι a → a < ε₀
𝔅ι-to-<ε₀ a good = h (good ⋆)
 where
  h : JointAff ι a → a < ε₀
  h (d , m , m+ , d<ε₀ , bnd) =
   ≤-trans (≤-S (transport (a ≤_) (ap (_⊗ ι[ m ]) (Z-left-unit d)) (bnd Z)))
           (⊗ι-<-ε₀ d m d<ε₀)

<ε₀-to-𝔅ι : (a : 𝓑) → a < ε₀ → 𝔅 ι a
<ε₀-to-𝔅ι a a<ε₀ _ =
 a , 1 , ≤-S ≤-Z , a<ε₀ ,
 (λ s → transport (a ≤_) ((Z-left-unit (s ⊕ a)) ⁻¹) (⊕-increasing-left s a))

\end{code}

The argument-shift lemma: a common upper bound `s ⊕ G` with constant `d` can
be re-read as bound `s` with constant `G ⊕ d` — by associativity of `⊕`
(no commutativity). This is what lets a ground argument be absorbed into the
constant when applying.

\begin{code}

JB-shift : (σ : type) (φ : Maj σ) (s G d : 𝓑) (m : ℕ)
         → JB σ φ (s ⊕ G) d m → JB σ φ s (G ⊕ d) m
JB-shift ι              a s G d m h =
 transport (a ≤_) (ap (_⊗ ι[ m ]) (⊕-assoc s G d)) h
JB-shift (ι ⇒ τ)        φ s G d m h =
 λ x x≤s → JB-shift τ (φ x) s G d m
             (h x (≤-trans x≤s (⊕-increasing-right s G)))
JB-shift ((σ ⇒ σ') ⇒ τ) φ s G d m h = h

\end{code}

Application closure. A function argument is fed straight through the
`FunArgs` tuple; a ground argument is absorbed into the constant via
`JB-shift`, with the common upper bound taken to dominate it.

\begin{code}

𝔅-app : (σ τ : type) (F : Maj (σ ⇒ τ)) (G : Maj σ)
      → 𝔅 (σ ⇒ τ) F → 𝔅 σ G → 𝔅 τ (F G)
𝔅-app (σ ⇒ σ') τ F G hF hG fa = hF ((G , hG) , fa)
𝔅-app ι         τ F G hF hG fa with hF fa
... | (d , m , m+ , d<ε₀ , jbnd) =
 (G ⊕ d) , m , m+ , ⊕-<-ε₀ G d (𝔅ι-to-<ε₀ G hG) d<ε₀ ,
 (λ s → JB-shift (GroundType τ) (plug τ (F G) fa) s G d m
          (jbnd (s ⊕ G) G (⊕-increasing-left s G)))

\end{code}

The base combinators are good.

\begin{code}

𝔅-Zero : 𝔅 ι Z
𝔅-Zero = <ε₀-to-𝔅ι Z Z<ε₀

𝔅-Succ : 𝔅 (ι ⇒ ι) (λ a → a)
𝔅-Succ _ = Z , 1 , ≤-S ≤-Z , Z<ε₀ ,
           (λ s x x≤s → transport (x ≤_) ((Z-left-unit s) ⁻¹) x≤s)

𝔅-Ω : 𝔅 (ι ⇒ ι) (λ a → S a)
𝔅-Ω _ = ι[ 1 ] , 1 , ≤-S ≤-Z , ι<ε₀ 1 ,
        (λ s x x≤s → transport ((S x) ≤_) ((Z-left-unit (S s)) ⁻¹) (≤-S x≤s))

\end{code}
