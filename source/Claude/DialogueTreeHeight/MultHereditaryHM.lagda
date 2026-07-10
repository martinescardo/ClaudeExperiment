Design H, *merged / doubled-budget* variant — a research fork of
`MultHereditaryH` aimed at the function-middle `S` combinator.

This is a PARALLEL line, kept alongside the original flat-pool tower (`H`,
`H2`–`H17`) rather than replacing it, so both the working all-ground result
and this attempt are on record. The only change to the predicate is in the
budget accounting: consuming a *function-typed* argument credits its budget
`2×` (`JH +ℕ (kbudget +ℕ kbudget)`), not `1×`.

Why: the function-middle `S` diagonal's ground leaf carries the shared
argument's budget `jγ` *twice* — once in the diagonal budget `jδ`, once as
`jγ` bumps inside the multiplier `Mδ` (feeding the function-value `γ a` to
`φ` charges both). The flat `1×` predicate credits a consumed function
argument only `1× jγ`, one short. Crediting `2×` supplies the second `jγ`;
since `bumpk` of any *finite* count preserves `< ε₀`, the extra budget is
free for the `< ε₀` goal. ⚠ HONEST STATUS (2026-07-08): this `2×`-budget fork is a DOCUMENTED DEAD END
for its stated purpose. It does NOT close the function-middle `S` obstruction.
The premise — that crediting a function argument `2×` its budget covers the
leaf deficit — rests on a flawed prototype (`MultHereditaryH18Proto`,
`fnmid-leaf-gen`, which inconsistently mixed the budget factor `m`). Under a
consistent factor the diagonal budget scales with `m` too: the fn-middle leaf
is `(m+1)·jγ` and the target `m·jγ`, so the deficit is `jγ` for every `m`
(scaling-invariant). The genuine obstruction is that `γ a`'s budget `jγ`
appears in the leaf BOTH as the value's budget cost and as its multiplier's
bump-count (`Mkg ≤ bumpk jγ Mγ`), while `kγ` supplies it once — the ordinal
cost of a function-typed intermediate result.

What this line IS: a correct, compiling reconstruction of the Howard tower
with function arguments credited `2×` budget — the recursor, `K`, base
combinators, and rebase all re-close (`HM3`–`HM7`), confirming that finite
budget is `< ε₀`-free. That reconstruction is sound; only the fn-middle
*payoff* fails. Kept as the record of the attempt. The conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryHM
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
open import Claude.DialogueTreeHeight.MultHereditaryH fe
 using (_+ℕ_)

\end{code}

Natural number addition (`_+ℕ_`) is shared with `MultHereditaryH` and the
budget/index arithmetic of `MultHereditaryH2`, so this fork's indices unify
with the reused (budget-agnostic) helper lemmas.

The hierarchy, exactly as `MultHereditaryH` except that consuming a
function-typed argument in `ZApply` credits its budget `2×`
(`JH +ℕ (kbudget +ℕ kbudget)`) — the one substantive change of this fork.

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
          (JH +ℕ (kbudget σ₁ σ₂ kh +ℕ kbudget σ₁ σ₂ kh))
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

The weakening toolkit: enlarging the additive accumulator weakens the bound,
uniformly. Every combinator closure threads through this. (Identical to
`MultHereditaryH`'s, retargeted at the doubled-budget accumulator.)

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
         (MH ⊕ kmult σ₁ σ₂ kh)
         (JH +ℕ (kbudget σ₁ σ₂ kh +ℕ kbudget σ₁ σ₂ kh)) D c M j
         (λ w → ⊕-mono-left (h w) (kadd σ₁ σ₂ kh w)) (z kh)

\end{code}
