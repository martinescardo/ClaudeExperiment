PROTOTYPE (not in the tour, not depended on): the **higher-type recursor** for
the affine-transformer predicate `JAff′` — iterating a *functional*
`F : (ι ⇒ ι) ⇒ (ι ⇒ ι)`.

Design note: `dialogue-tree-height-decoupling.md`. `MultDominated.MDom-orbit`
already closes the *ground* recursor (iterating `φ : 𝓑 → 𝓑`), with the
multiplier raised `M ↦ ω^(M ⊗ ω)`. The *function-typed* recursor is the case the
user flagged ("iterators increase their strength with type level", CSL 2011) and
that `MultOrbit`'s header names as **the open kernel**: that a functional's
per-step multiplicative factor genuinely is a fixed `m < ε₀`, carried
hereditarily.

The transformer predicate supplies exactly that. Feeding an argument of
multiplier `M₁` to `F` (data `D_F, c_F, M_F`) yields output multiplier
`(M₁ ⊗ ω) ⊗ M_F = M₁ ⊗ (ω ⊗ M_F)` (associativity) — a **fixed** factor
`m = ω ⊗ M_F < ε₀`, independent of the iteration count. So iterating `F` splits
into three orbits on the affine data:

* `D` stays `D_F` (the argument's accumulator absorbs into the multiplier — the
  `nested-a-absorb` crux), so it remains `GoodT`;
* `c` is an **additive** orbit `cₖ₊₁ = cₖ ⊕ c_F` — sup `≤ c_g ⊕ (c_F ⊗ ω) < ε₀`
  via `Orbit.orbit-sup-≤`;
* `M` is a **multiplicative** orbit `Mₖ₊₁ = Mₖ ⊗ (ω ⊗ M_F)` with fixed factor —
  sup `≤ M_g ⊗ ω^((ω ⊗ M_F) ⊗ ω) < ε₀` via `MultOrbit.orbit-mult-sup-≤`.

The payoff `JAff′-Iter-fn`: from `JAff′` of the functional `F` and the start `g`,
the pointwise-sup iterate `λ T₁ w → L (λ k → iter F g k T₁ w)` is `JAff′` again.
This is the recursor closure at one type level *above* ground — the level whose
factor `ω ⊗ M_F` climbs the tower as `M_F` does. It resolves `MultOrbit`'s open
kernel **for the affine-transformer class**: the fixed factor is not assumed, it
is read off the predicate.

Honest scope. This is the recursor *step* assuming the components are `JAff′`
(the logical-relations shape). It does not by itself prove the fundamental
theorem — the remaining cases (`K`, application, and the recursor at *arbitrary*
type levels, where `σ₂` is itself higher) are the development this underpins. The
conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.IterFnProto
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import Claude.BrouwerOrdinals.Order fe
 using (_≤_ ; _⊕_ ; ≤-refl ; ≤-trans ; ≤-L-upper-bound)
open import Claude.BrouwerOrdinals.Orbit fe using (ω ; _⊗_ ; orbit-sup-≤)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ω^_ ; ⊗-mono-right ;
        ⊕-<-ε₀ ; ⊕-increasing-right ; tower-<-ε₀)
open import Claude.BrouwerOrdinals.Affine fe using (⊗-assoc ; ⊕-increasing-left)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (⊗-<-ε₀)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; validMult-⊗ ; validMult-orbit ; ω-valid)
open import Claude.BrouwerOrdinals.MultOrbit fe using (orbit-mult-sup-≤ ; pw-sup-≤)
open import Claude.DialogueTreeHeight.MultHereditaryF fe
 using (𝕋 ; GoodT ; GoodT-⊕)
open import Claude.DialogueTreeHeight.AffTransformerPredicate fe
 using (BoundT′ ; JAff′ ; sup-𝕋 ; BoundT′-L ;
        BoundT′-mono-D ; BoundT′-mono-c ; BoundT′-mono-M)

\end{code}

The higher-type recursor closes **at every type level**: iterating a `JAff′`
functional `F : (σ₁ ⇒ σ₂) ⇒ (σ₁ ⇒ σ₂)` on a `JAff′` start `g : σ₁ ⇒ σ₂` stays
`JAff′`. The orbit data (`Dk`, `ck`, `Mk`) and their domination are
*level-independent* — the transformer clause's recurrence does not depend on
`σ₂` — so the only level-sensitive step is the final assembly: bring each
iterate's data up to the fixed `(D∞ , c∞ , M∞)` with the three monotonicity
lemmas, then take the pointwise sup with `BoundT′-L`.

\begin{code}

JAff′-Iter-fn : (σ₁ σ₂ : type)
                (F : 𝕋 ((σ₁ ⇒ σ₂) ⇒ (σ₁ ⇒ σ₂))) (g : 𝕋 (σ₁ ⇒ σ₂))
              → JAff′ ((σ₁ ⇒ σ₂) ⇒ (σ₁ ⇒ σ₂)) F → JAff′ (σ₁ ⇒ σ₂) g
              → JAff′ (σ₁ ⇒ σ₂) (sup-𝕋 (σ₁ ⇒ σ₂) (iter F g))
JAff′-Iter-fn σ₁ σ₂ F g
  (D_F , c_F , M_F , gD_F , c_Fε , vM_F , bF)
  (D_g , c_g , M_g , gD_g , c_gε , vM_g , bg) =
    D∞ , c∞ , M∞ , gD∞ , c∞<ε₀ , vM∞ , boundL
 where
  σ : type
  σ = σ₁ ⇒ σ₂

  D∞ : 𝓑 → 𝓑
  D∞ w = D_g w ⊕ D_F w

  gD∞ : GoodT ι D∞
  gD∞ = GoodT-⊕ D_g D_F gD_g gD_F

  m : 𝓑
  m = ω ⊗ M_F

  ω<ε₀ : ω < ε₀
  ω<ε₀ = tower-<-ε₀ 0

  c∞ : 𝓑
  c∞ = c_g ⊕ (c_F ⊗ ω)

  c∞<ε₀ : c∞ < ε₀
  c∞<ε₀ = ⊕-<-ε₀ c_g (c_F ⊗ ω) c_gε (⊗-<-ε₀ c_F ω c_Fε ω<ε₀)

  M∞ : 𝓑
  M∞ = M_g ⊗ ω^ (m ⊗ ω)

  vM∞ : ValidMult M∞
  vM∞ = validMult-⊗ vM_g (validMult-orbit (validMult-⊗ ω-valid vM_F))

  Dk : ℕ → (𝓑 → 𝓑)
  Dk zero     = D_g
  Dk (succ k) = D_F

  ck : ℕ → 𝓑
  ck zero     = c_g
  ck (succ k) = ck k ⊕ c_F

  Mk : ℕ → 𝓑
  Mk zero     = M_g
  Mk (succ k) = (Mk k ⊗ ω) ⊗ M_F

  ckε : (k : ℕ) → ck k < ε₀
  ckε zero     = c_gε
  ckε (succ k) = ⊕-<-ε₀ (ck k) c_F (ckε k) c_Fε

  vMk : (k : ℕ) → ValidMult (Mk k)
  vMk zero     = vM_g
  vMk (succ k) = validMult-⊗ (validMult-⊗ (vMk k) ω-valid) vM_F

\end{code}

The per-count bound: `iter F g k`, as a function, has the affine data
`(Dk k, ck k, Mk k)`. Base is `g`'s bound; the step feeds the previous iterate
into `F`'s transformer clause — the recurrences are then definitional.

\begin{code}

  bnd : (k : ℕ) → BoundT′ σ (iter F g k) (Dk k) (ck k) (Mk k)
  bnd zero     = bg
  bnd (succ k) = bF (iter F g k) (Dk k) (ck k) (Mk k) (ckε k) (vMk k) (bnd k)

\end{code}

The three orbits dominate into fixed `< ε₀` data.

\begin{code}

  Dk≤ : (k : ℕ) (w : 𝓑) → Dk k w ≤ D∞ w
  Dk≤ zero     w = ⊕-increasing-right (D_g w) (D_F w)
  Dk≤ (succ k) w = ⊕-increasing-left (D_g w) (D_F w)

  ck≤ : (k : ℕ) → ck k ≤ c∞
  ck≤ k = ≤-trans (≤-L-upper-bound ck k)
                  (orbit-sup-≤ ck c_F (λ j → ≤-refl (ck j ⊕ c_F)))

  Mk≤ : (k : ℕ) → Mk k ≤ M∞
  Mk≤ k = ≤-trans (≤-L-upper-bound Mk k)
            (≤-trans (orbit-mult-sup-≤ Mk m stepM)
                     (⊗-mono-right M_g (pw-sup-≤ m)))
   where
    stepM : (j : ℕ) → Mk (succ j) ≤ (Mk j ⊗ m)
    stepM j = transport (λ z → Mk (succ j) ≤ z)
                        (⊗-assoc (Mk j) ω M_F) (≤-refl (Mk (succ j)))

\end{code}

Assembling: bring each iterate's data up to the fixed `(D∞ , c∞ , M∞)` with the
three monotonicity lemmas, then take the pointwise sup with `BoundT′-L`.

\begin{code}

  bnd′ : (k : ℕ) → BoundT′ σ (iter F g k) D∞ c∞ M∞
  bnd′ k =
   BoundT′-mono-M σ (iter F g k) D∞ c∞ (Mk k) M∞ (Mk≤ k)
     (BoundT′-mono-c σ (iter F g k) D∞ (ck k) c∞ (Mk k) (ck≤ k)
       (BoundT′-mono-D σ (iter F g k) (Dk k) D∞ (ck k) (Mk k) (Dk≤ k)
         (bnd k)))

  boundL : BoundT′ σ (sup-𝕋 σ (iter F g)) D∞ c∞ M∞
  boundL = BoundT′-L σ (iter F g) D∞ c∞ M∞ bnd′

\end{code}
