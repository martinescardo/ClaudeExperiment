Design H, stage 1: the Howard-tower tracked-data hierarchy — the predicate.

This module defines the level-free form of the Howard tower designed in
`dialogue-tree-height-howard-tower.md` and prepared by modules 45–47: a
type-indexed hierarchy `𝕂` of *tracked data*, where an arrow-typed datum is
a map together with a **zone pack** — a joint affine bound with a
multiplier pool and a bump budget (`MultBump`) — and, crucially, where the
bound *constrains the packs of partial applications* (`PackDom`): the
additive part of a partial application's own pack is dominated by the
current zone, its multiplier by the current pool, its budget by the current
budget. This last clause is the "rigid multiplier" invariant that closes
the ground-`S` diagonal at function-typed middles: the pack of `γ a` is
forced to be affine in `a`'s bound with fixed multiplier data *by the shape
of the predicate*, so the diagonal's pack can be assembled arithmetically
(the `JAff-Sg-diag`/`Tracked-diag` pattern) instead of demanding another
storey — the self-similar regress of module 45 terminates here.

The accumulators, threaded through the argument spine:

* `A : 𝓑 → 𝓑` — the additive zone: ground arguments contribute their bound
  functions, function arguments their packs' additive parts (`kadd`);
* `MH : 𝓑` — the multiplier pool: function arguments contribute their
  packs' multipliers (`kmult`);
* `JH : ℕ` — the bump budget: function arguments contribute their packs'
  budgets (`kbudget`, in semantic form).

At ground the bound is `pr₁ k w ≤ ((D w ⊕ (A w ⊕ c)) ⊗ bumpk (j + JH)
(M ⊕ MH))` — a single zone, multiplied by the pooled multipliers under the
pooled budget of bumps; `MultBump`'s absorption laws are exactly what makes
consuming the pool sound (products of pool elements cost one bump, the
recursor's raise is one bump).

Stage 1 content: the mutual definition (structural on types — `ZApply`
consumes one argument, `ZCont` continues; a `𝕂` at the argument type and
the result type are both proper subterms), the projections, and the
weakening toolkit in the additive accumulator (`ZCont-mono-A`), which every
combinator closure uses. The combinator packs and the fundamental theorem
over `T₁` are the next stage; the conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryH
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe
 using (ω ; _⊗_ ; ⊕-mono-left)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult)
open import Claude.DialogueTreeHeight.MultHereditaryF fe
 using (GoodT)
open import Claude.DialogueTreeHeight.MultHereditaryG fe
 using (GFun)
open import Claude.BrouwerOrdinals.MultBump fe
 using (bumpk)

\end{code}

Natural number addition, locally (to avoid clashing with the coproduct).

\begin{code}

_+ℕ_ : ℕ → ℕ → ℕ
zero   +ℕ n = n
succ m +ℕ n = succ (m +ℕ n)

\end{code}

The hierarchy. `𝕂 ι` is a good bound function; `𝕂 (σ ⇒ τ)` is a map with a
zone pack. `ZApply` consumes one argument (ground: its bound function joins
the zone; function-typed: its pack's parts join the accumulators), `ZCont`
continues through the result type, constraining partial applications' packs
(`PackDom`) on the way.

\begin{code}

𝕂       : type → 𝓤₀ ̇
ZPack   : (σ τ : type) → (𝕂 σ → 𝕂 τ) → 𝓤₀ ̇
ZApply  : (σ τ : type) → (𝕂 σ → 𝕂 τ)
        → (𝓑 → 𝓑) → 𝓑 → ℕ → (𝓑 → 𝓑) → 𝓑 → 𝓑 → ℕ → 𝓤₀ ̇
ZCont   : (τ : type) → 𝕂 τ
        → (𝓑 → 𝓑) → 𝓑 → ℕ → (𝓑 → 𝓑) → 𝓑 → 𝓑 → ℕ → 𝓤₀ ̇
PackDom : (σ τ : type) → 𝕂 (σ ⇒ τ)
        → (𝓑 → 𝓑) → 𝓑 → ℕ → (𝓑 → 𝓑) → 𝓑 → 𝓑 → ℕ → 𝓤₀ ̇
kadd    : (σ τ : type) → 𝕂 (σ ⇒ τ) → 𝓑 → 𝓑
kmult   : (σ τ : type) → 𝕂 (σ ⇒ τ) → 𝓑
kbudget : (σ τ : type) → 𝕂 (σ ⇒ τ) → ℕ

𝕂 ι       = GFun
𝕂 (σ ⇒ τ) = Σ F ꞉ (𝕂 σ → 𝕂 τ) , ZPack σ τ F

ZPack σ τ F = Σ D ꞉ (𝓑 → 𝓑) , Σ c ꞉ 𝓑 , Σ M ꞉ 𝓑 , Σ j ꞉ ℕ ,
                 GoodT ι D × (c < ε₀) × ValidMult M × (M < ε₀)
               × ZApply σ τ F (λ _ → Z) Z 0 D c M j

ZApply ι         τ F A MH JH D c M j =
 (b : GFun) → ZCont τ (F b) (λ w → A w ⊕ pr₁ b w) MH JH D c M j
ZApply (σ₁ ⇒ σ₂) τ F A MH JH D c M j =
 (kh : 𝕂 (σ₁ ⇒ σ₂))
  → ZCont τ (F kh)
          (λ w → A w ⊕ kadd σ₁ σ₂ kh w)
          (MH ⊕ kmult σ₁ σ₂ kh)
          (JH +ℕ kbudget σ₁ σ₂ kh)
          D c M j

ZCont ι       k A MH JH D c M j =
 (w : 𝓑) → pr₁ k w ≤ ((D w ⊕ (A w ⊕ c)) ⊗ bumpk (j +ℕ JH) (M ⊕ MH))
ZCont (σ ⇒ τ) k A MH JH D c M j =
   PackDom σ τ k A MH JH D c M j
 × ZApply σ τ (pr₁ k) A MH JH D c M j

PackDom σ τ k A MH JH D c M j =
   ((w : 𝓑) → kadd σ τ k w
                ≤ ((D w ⊕ (A w ⊕ c)) ⊗ bumpk (j +ℕ JH) (M ⊕ MH)))
 × (kmult σ τ k ≤ bumpk (j +ℕ JH) (M ⊕ MH))
 × ((P : 𝓑) → bumpk (kbudget σ τ k) P ≤ bumpk (j +ℕ JH) P)

kadd    σ τ (F , D , c , M , j , _) = λ w → D w ⊕ c
kmult   σ τ (F , D , c , M , j , _) = M
kbudget σ τ (F , D , c , M , j , _) = j

\end{code}

The weakening toolkit: enlarging the additive accumulator weakens the
bound, uniformly. (No contravariance arises: argument data is universally
quantified, and `PackDom`'s zone is covariant in `A`.) Every combinator
closure threads through this.

\begin{code}

zone-mono-A : (A A′ D : 𝓑 → 𝓑) (c P : 𝓑)
            → ((w : 𝓑) → A w ≤ A′ w)
            → (w : 𝓑)
            → ((D w ⊕ (A w ⊕ c)) ⊗ P) ≤ ((D w ⊕ (A′ w ⊕ c)) ⊗ P)
zone-mono-A A A′ D c P h w =
 ⊗-mono-left (⊕-mono-right (D w) (⊕-mono-left (h w) c)) P

ZCont-mono-A  : (τ : type) (k : 𝕂 τ) (A A′ : 𝓑 → 𝓑) (MH : 𝓑) (JH : ℕ)
                (D : 𝓑 → 𝓑) (c M : 𝓑) (j : ℕ)
              → ((w : 𝓑) → A w ≤ A′ w)
              → ZCont τ k A MH JH D c M j
              → ZCont τ k A′ MH JH D c M j
ZApply-mono-A : (σ τ : type) (F : 𝕂 σ → 𝕂 τ) (A A′ : 𝓑 → 𝓑) (MH : 𝓑) (JH : ℕ)
                (D : 𝓑 → 𝓑) (c M : 𝓑) (j : ℕ)
              → ((w : 𝓑) → A w ≤ A′ w)
              → ZApply σ τ F A MH JH D c M j
              → ZApply σ τ F A′ MH JH D c M j

ZCont-mono-A ι k A A′ MH JH D c M j h z =
 λ w → ≤-trans (z w)
        (zone-mono-A A A′ D c (bumpk (j +ℕ JH) (M ⊕ MH)) h w)
ZCont-mono-A (σ ⇒ τ) k A A′ MH JH D c M j h ((pd , pm , pj) , z) =
 ( (λ w → ≤-trans (pd w)
           (zone-mono-A A A′ D c (bumpk (j +ℕ JH) (M ⊕ MH)) h w))
 , pm , pj )
 , ZApply-mono-A σ τ (pr₁ k) A A′ MH JH D c M j h z

ZApply-mono-A ι         τ F A A′ MH JH D c M j h z =
 λ b → ZCont-mono-A τ (F b)
        (λ w → A w ⊕ pr₁ b w) (λ w → A′ w ⊕ pr₁ b w) MH JH D c M j
        (λ w → ⊕-mono-left (h w) (pr₁ b w)) (z b)
ZApply-mono-A (σ₁ ⇒ σ₂) τ F A A′ MH JH D c M j h z =
 λ kh → ZCont-mono-A τ (F kh)
         (λ w → A w ⊕ kadd σ₁ σ₂ kh w) (λ w → A′ w ⊕ kadd σ₁ σ₂ kh w)
         (MH ⊕ kmult σ₁ σ₂ kh) (JH +ℕ kbudget σ₁ σ₂ kh) D c M j
         (λ w → ⊕-mono-left (h w) (kadd σ₁ σ₂ kh w)) (z kh)

\end{code}

Stage 2 — the combinator packs (`K`, `S`, the base combinators, and the
recursor via `MultHereditaryG`'s orbit engine consuming the pack at
`ι ⇒ ι`), the bound relation tying `𝕂` to the Design-F transformers, and
the fundamental theorem over `T₁` — continues from here.
