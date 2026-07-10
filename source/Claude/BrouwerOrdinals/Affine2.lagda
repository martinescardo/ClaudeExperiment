The two-argument jointly-affine class and the S-diagonal (constructive).

The single-argument affine class `Aff` (`AffineClosure`) closes application,
composition, constants and partial iteration — everything *except* the `S`
diagonal `λ a → φ a (γ a)`, where one ground argument `a` is shared between a
two-argument function `φ` and its second argument `γ a`. That sharing needs a
**two-argument jointly-affine** bound on `φ`, which this module provides.

Following `Hereditary`, the joint bound is taken *relative to a common upper
bound* `s` on both arguments — `φ a b ≤ (s ⊕ d) ⊗ ι[m]` whenever `a ≤ s` and
`b ≤ s`. The common bound makes it symmetric in the two arguments, so the
proofs reorder them using only associativity of `⊕` (never commutativity,
which fails for the ordinal sum).

The crux is `Aff2-diag`: **a jointly-affine `φ` diagonalised against an affine
`γ` is (single-argument) affine.** This is exactly the `S`-combinator closure
the wall is about, and it goes through by the *same* technique as `Aff-∘` —
take the common bound `s = (a ⊕ e) ⊗ ι[n]` (which dominates both `a` and
`γ a`, the latter by affineness of `γ`), then fold with `affine-fold-num`.

Scope, honestly: the multiplier here is a *finite* `ι[m]`. The
jointly-affine functions with a finite multiplier are those built from
projections, constants, single-argument affines and sums (all provided). The
recursor `Iter f : ι ⇒ ι ⇒ ι` is jointly affine only with an `ω`-multiplier
(its orbit sup is `(a ⊕ d ⊗ ω) ⊗ ω`), which the `⊗`-fold does not reach — that
needs the natural-sum (`OmegaPoly`) route. So this module supplies the
finite-multiplier half of the `S`-diagonal closure; the `ω`-multiplier half is
the identified next step.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.BrouwerOrdinals.Affine2
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import Claude.BrouwerOrdinals.Order fe
open import Claude.BrouwerOrdinals.Orbit fe
 using (ι[_] ; _⊗_ ; ⊕-assoc ; ⊕-mono-left)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ⊕-<-ε₀ ; ⊗-mono-left ; ⊕-increasing-right ; Z-left-unit)
open import Claude.BrouwerOrdinals.Affine fe
 using (affine-fold-num ; ⊗-assoc ; _·ℕ_ ; ι-*-homo ; one-≤-⊗ ; affine-orbit-<-ε₀)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (Aff ; Aff-app ; x-≤-x⊗ ; Z<ε₀ ; ⊗ι-<-ε₀)

\end{code}

The two-argument jointly-affine class, relative to a common upper bound.

\begin{code}

Aff2 : (𝓑 → 𝓑 → 𝓑) → 𝓤₀ ̇
Aff2 φ = Σ m ꞉ ℕ , Σ d ꞉ 𝓑 ,
           (S Z ≤ ι[ m ]) × (d < ε₀)
           × ((s a b : 𝓑) → a ≤ s → b ≤ s → φ a b ≤ ((s ⊕ d) ⊗ ι[ m ]))

\end{code}

The projections are jointly affine (`m = 1`, `d = Z`): each argument is `≤ s`,
and `(s ⊕ Z) ⊗ ι[ 1 ]` reduces to `Z ⊕ s`.

\begin{code}

Aff2-π₁ : Aff2 (λ a b → a)
Aff2-π₁ = 1 , Z , ≤-S ≤-Z , Z<ε₀ ,
          (λ s a b a≤s b≤s → transport (a ≤_) ((Z-left-unit s) ⁻¹) a≤s)

Aff2-π₂ : Aff2 (λ a b → b)
Aff2-π₂ = 1 , Z , ≤-S ≤-Z , Z<ε₀ ,
          (λ s a b a≤s b≤s → transport (b ≤_) ((Z-left-unit s) ⁻¹) b≤s)

\end{code}

A single-argument affine function, read as a two-argument one that ignores the
other argument, is jointly affine — in either slot. (The common bound `s`
dominates the used argument, and monotonicity does the rest.)

\begin{code}

Aff-to-Aff2-left : {φ : 𝓑 → 𝓑} → Aff φ → Aff2 (λ a b → φ a)
Aff-to-Aff2-left (m , d , m+ , d<ε₀ , bound) =
 m , d , m+ , d<ε₀ ,
 (λ s a b a≤s b≤s → ≤-trans (bound a) (⊗-mono-left (⊕-mono-left a≤s d) ι[ m ]))

Aff-to-Aff2-right : {φ : 𝓑 → 𝓑} → Aff φ → Aff2 (λ a b → φ b)
Aff-to-Aff2-right (m , d , m+ , d<ε₀ , bound) =
 m , d , m+ , d<ε₀ ,
 (λ s a b a≤s b≤s → ≤-trans (bound b) (⊗-mono-left (⊕-mono-left b≤s d) ι[ m ]))

\end{code}

The crux — the `S` diagonal. A jointly-affine `φ` diagonalised against an
affine `γ` is single-argument affine. The common bound is
`s = (a ⊕ e) ⊗ ι[ n ]`: it dominates `a` (increasing, then `x-≤-x⊗`) and
`γ a` (affineness of `γ`). Feeding both into the joint bound and folding with
`affine-fold-num` gives `φ a (γ a) ≤ (a ⊕ (e ⊕ d)) ⊗ ι[ n ·ℕ m ]` — affine,
exactly as in `Aff-∘`.

\begin{code}

Aff2-diag : {φ : 𝓑 → 𝓑 → 𝓑} {γ : 𝓑 → 𝓑}
          → Aff2 φ → Aff γ → Aff (λ a → φ a (γ a))
Aff2-diag {φ} {γ} (m , d , m+ , d<ε₀ , jb) (n , e , n+ , e<ε₀ , gb) =
 (n ·ℕ m) , (e ⊕ d) , nm+ , ⊕-<-ε₀ e d e<ε₀ d<ε₀ , bound
 where
  nm+ : S Z ≤ ι[ n ·ℕ m ]
  nm+ = transport (S Z ≤_) (ι-*-homo n m) (one-≤-⊗ ι[ n ] ι[ m ] n+ m+)

  bound : (a : 𝓑) → φ a (γ a) ≤ ((a ⊕ (e ⊕ d)) ⊗ ι[ n ·ℕ m ])
  bound a = transport (λ z → φ a (γ a) ≤ (z ⊗ ι[ n ·ℕ m ])) (⊕-assoc a e d) chain
   where
    s : 𝓑
    s = (a ⊕ e) ⊗ ι[ n ]

    a≤s : a ≤ s
    a≤s = ≤-trans (⊕-increasing-right a e) (x-≤-x⊗ (a ⊕ e) ι[ n ] n+)

    γa≤s : γ a ≤ s
    γa≤s = gb a

    step0 : φ a (γ a) ≤ ((s ⊕ d) ⊗ ι[ m ])
    step0 = jb s a (γ a) a≤s γa≤s

    inner : (s ⊕ d) ≤ (((a ⊕ e) ⊕ d) ⊗ ι[ n ])
    inner = affine-fold-num (a ⊕ e) d n n+

    assoc-eq : ((((a ⊕ e) ⊕ d) ⊗ ι[ n ]) ⊗ ι[ m ])
             ＝ (((a ⊕ e) ⊕ d) ⊗ ι[ n ·ℕ m ])
    assoc-eq = ⊗-assoc ((a ⊕ e) ⊕ d) ι[ n ] ι[ m ]
             ∙ ap (((a ⊕ e) ⊕ d) ⊗_) (ι-*-homo n m)

    chain : φ a (γ a) ≤ (((a ⊕ e) ⊕ d) ⊗ ι[ n ·ℕ m ])
    chain = transport (λ z → φ a (γ a) ≤ z) assoc-eq
                      (≤-trans step0 (⊗-mono-left inner ι[ m ]))

\end{code}

Application of a jointly-affine function to two sub-`ε₀` arguments stays
`< ε₀`: take the common bound `s = x ⊕ y`, and the joint bound plus `ε₀`
closure under `⊕`, `⊗ ι[ m ]` does the rest. (`⊗ ι[ m ] < ε₀` via the
`AffineClosure` toolkit; here we phrase it through `Aff2-diag` against the
constant `γ = λ _ → y`, reusing `Aff-app` downstream — kept minimal, the
diagonal is the point.)

\begin{code}

Aff2-app : {φ : 𝓑 → 𝓑 → 𝓑} → Aff2 φ
         → (x y : 𝓑) → x ≤ y → y < ε₀ → φ x y < ε₀
Aff2-app {φ} (m , d , m+ , d<ε₀ , jb) x y x≤y y<ε₀ =
 ≤-trans (≤-S (jb y x y x≤y (≤-refl y))) (⊗ι-<-ε₀ (y ⊕ d) m (⊕-<-ε₀ y d y<ε₀ d<ε₀))

\end{code}

The `ω`-multiplier case — the recursor as a two-argument function. A partial
recursor `Iter f : ι ⇒ ι ⇒ ι` has majorant `λ a ν → L (λ k → iter φ a k) ⊕ ν`,
which is jointly affine only with an **`ω`-multiplier** (its orbit supremum,
as a function of the start `a`, is `(a ⊕ d ⊗ ω) ⊗ ω` — `Affine.affine-orbit`).
The `⊗`-fold `(x ⊗ M ⊕ d) ≤ (x ⊕ d) ⊗ M` that `Aff2-diag` runs on is *false*
for a limit multiplier `M`, so this function is **not** in any finite-multiplier
`Aff2` — and worse, `ω`-affine functions are not closed under composition (two
of them compose to `ω²`). That non-closure is precisely the type-level tower
`ω ↑↑ ℓ`: the open conjecture, not a gap to be patched.

What *is* available — and clean — is the **pointwise** bound. A predicate that
asks only for `< ε₀` outputs on `< ε₀` inputs (no uniform multiplier, so no
composition requirement) *does* hold for the recursor, via `affine-orbit-<-ε₀`,
and the `S`-diagonal against it is `< ε₀` pointwise. This is the honest ceiling
of the `⊗`-affine route for the recursor: the diagonal is bounded whenever
*applied*, but not in a class closed under further composition or iteration.

\begin{code}

Aff-orbit-<-ε₀ : {φ : 𝓑 → 𝓑} → Aff φ
               → (a : 𝓑) → a < ε₀ → L (λ k → iter φ a k) < ε₀
Aff-orbit-<-ε₀ {φ} (succ p , d , _ , d<ε₀ , bound) a a<ε₀ =
 affine-orbit-<-ε₀ φ d p bound d<ε₀ a a<ε₀

Good2 : (𝓑 → 𝓑 → 𝓑) → 𝓤₀ ̇
Good2 φ = (a b : 𝓑) → a < ε₀ → b < ε₀ → φ a b < ε₀

Good2-Iter : {φ : 𝓑 → 𝓑} → Aff φ
           → Good2 (λ a ν → L (λ k → iter φ a k) ⊕ ν)
Good2-Iter Aφ a ν a<ε₀ ν<ε₀ =
 ⊕-<-ε₀ (L (λ k → iter _ a k)) ν (Aff-orbit-<-ε₀ Aφ a a<ε₀) ν<ε₀

Good2-diag : {φ : 𝓑 → 𝓑 → 𝓑} {γ : 𝓑 → 𝓑} → Good2 φ → Aff γ
           → (a : 𝓑) → a < ε₀ → φ a (γ a) < ε₀
Good2-diag {φ} {γ} g2 Aγ a a<ε₀ = g2 a (γ a) a<ε₀ (Aff-app Aγ a a<ε₀)

\end{code}

Combining the two: the `S`-diagonal of a partial recursor against an affine
function — `S (Iter f) γ = λ a → Iter f a (γ a)`, iterate `f` from `a` for
`γ a` steps — has majorant `< ε₀` at every `< ε₀` argument. This is the
recursor `S`-diagonal, bounded pointwise (the maximal unconditional statement
before the tower).

\begin{code}

recursor-diag-<-ε₀ : {φ : 𝓑 → 𝓑} {γ : 𝓑 → 𝓑} → Aff φ → Aff γ
                   → (a : 𝓑) → a < ε₀ → (L (λ k → iter φ a k) ⊕ γ a) < ε₀
recursor-diag-<-ε₀ Aφ Aγ = Good2-diag (Good2-Iter Aφ) Aγ

\end{code}
