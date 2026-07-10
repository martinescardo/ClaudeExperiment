Design H, stage 2d(iii): the `K` combinator over the Howard tower —
`GoodH-K`, fully polymorphic.

The constant function's tower datum reflects its argument (`reflect`: at
ground the self-datum, at arrows the datum the argument's own `LT`
carries), and the packs are instantiations of the stage-2b rebase:

* `ccore`: the constant map's continuation under the pack built from the
  argument's own zone data (`kD`/`kM`/`kJ`), the rebase at `u = ja , e = 0`
  making the concluding budget *equal* the pack budget `rbb (σ₁⇒σ₂) ja 0`;
* `ocore-ι`/`ocore-fn`: the argument re-bounded under the *outer* trivial
  pack `(Z , Z , ω , rbb σ 0 0)` once its contributions sit in the
  accumulators — the rebase at `u = e = 0`, concluding budget exactly the
  outer budget.

The budget bookkeeping uses the `u`-independent split constant
`rbc`/`rbb-＝` (`rbb τ u e ＝ u + rbc τ e`): pack budgets are chosen before
arguments arrive, and `rbb σ ja 0 ＝ rbb σ 0 0 + ja` (by commutativity) is
what lets the argument's budget flow through the accumulator — the `K`
combinator is budget-neutral. The conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryH7
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe
 using (ω ; _⊗_ ; ⊕-mono-left)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right ;
        ⊕-increasing-right ; ⊕-<-ε₀ ; tower-<-ε₀)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊕-increasing-left)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (⊗-<-ε₀)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (x-≤-x⊗ ; y-≤-⊗ ; Z<ε₀)
open import Claude.BrouwerOrdinals.MultAffine fe using (ω-pos)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; ω-valid ; validMult-⊗)
open import Claude.DialogueTreeHeight.Majorant fe
 using (Maj ; μ-K)
open import Claude.DialogueTreeHeight.MultHereditaryF fe
 using (𝕋 ; GoodT)
open import Claude.BrouwerOrdinals.MultBump fe
 using (bump ; bumpk ; bumpk-mono ; ≤-bump ; ⊗-≤-bump)
open import Claude.DialogueTreeHeight.MultHereditaryH fe
 using (_+ℕ_ ; 𝕂 ; ZPack ; ZApply ; ZCont ; PackDom ;
        kadd ; kmult ; kbudget)
open import Claude.DialogueTreeHeight.MultHereditaryH2 fe
 using (+ℕ-zero-right ; +ℕ-succ-right ; +ℕ-comm ; +ℕ-assoc ;
        bumpk-+ ; ≤-bumpk ; bumpk-pad ; rbb)
open import Claude.DialogueTreeHeight.MultHereditaryH3 fe
 using (ZApply-rebase ; rbb-split)
open import Claude.DialogueTreeHeight.MultHereditaryH4 fe
 using (BndH ; LT ; BndL ; GoodH ; ⊕-Z-left)

\end{code}

Budget arithmetic: the `u`-independent split constant, and left padding.

\begin{code}

rbc : type → ℕ → ℕ
rbc ι               e = succ e
rbc (ι ⇒ τ)         e = succ (rbc τ e)
rbc ((σ₁ ⇒ σ₂) ⇒ τ) e = succ (rbc τ (succ e))

rbb-＝ : (τ : type) (u e : ℕ) → rbb τ u e ＝ (u +ℕ rbc τ e)
rbb-＝ ι               u e = (+ℕ-succ-right u e) ⁻¹
rbb-＝ (ι ⇒ τ)         u e =
 rbb-＝ τ (succ u) e ∙ ((+ℕ-succ-right u (rbc τ e)) ⁻¹)
rbb-＝ ((σ₁ ⇒ σ₂) ⇒ τ) u e =
 rbb-＝ τ (succ u) (succ e) ∙ ((+ℕ-succ-right u (rbc τ (succ e))) ⁻¹)

bumpk-pad-left : (b a : ℕ) (P : 𝓑) → bumpk a P ≤ bumpk (b +ℕ a) P
bumpk-pad-left b a P =
 transport (λ z → bumpk a P ≤ z) ((bumpk-+ b a P) ⁻¹)
           (≤-bumpk b (bumpk a P))

\end{code}

Reflection: every transformer's `LT` yields a tower datum bounding it.

\begin{code}

reflect : (σ : type) (T : 𝕋 σ) → LT σ T → Σ k ꞉ 𝕂 σ , BndH σ T k
reflect ι       T lT = (T , lT) , (λ w → ≤-refl (T w))
reflect (σ ⇒ τ) T lT = pr₂ lT

\end{code}

The constant pack's data, built from the argument's datum.

\begin{code}

kD : (σ : type) → 𝕂 σ → 𝓑 → 𝓑
kD ι         k = pr₁ k
kD (σ₁ ⇒ σ₂) k = kadd σ₁ σ₂ k

kM : (σ : type) → 𝕂 σ → 𝓑
kM ι         k = ω
kM (σ₁ ⇒ σ₂) k = kmult σ₁ σ₂ k ⊗ ω

kJ : (σ : type) → 𝕂 σ → ℕ
kJ ι         k = 0
kJ (σ₁ ⇒ σ₂) k = rbb (σ₁ ⇒ σ₂) (kbudget σ₁ σ₂ k) 0

kD-good : (σ : type) (k : 𝕂 σ) → GoodT ι (kD σ k)
kD-good ι         k = pr₂ k
kD-good (σ₁ ⇒ σ₂) (F , D , c , M , j , gD , cε , vM , Mε , za) =
 (λ w p → ⊕-<-ε₀ (D w) c (pr₁ gD w p) cε)
 , (λ w w′ q → ⊕-mono-left (pr₂ gD w w′ q) c)

kM-valid : (σ : type) (k : 𝕂 σ) → ValidMult (kM σ k)
kM-valid ι         k = ω-valid
kM-valid (σ₁ ⇒ σ₂) (F , D , c , M , j , gD , cε , vM , Mε , za) =
 validMult-⊗ vM ω-valid

kM-ε : (σ : type) (k : 𝕂 σ) → kM σ k < ε₀
kM-ε ι         k = tower-<-ε₀ 0
kM-ε (σ₁ ⇒ σ₂) (F , D , c , M , j , gD , cε , vM , Mε , za) =
 ⊗-<-ε₀ M ω Mε (tower-<-ε₀ 0)

\end{code}

The constant-map continuation `ccore`: the argument, bounded under its own
zone-data pack, at arbitrary accumulators.

\begin{code}

ccore : (σ : type) (ka : 𝕂 σ) (A : 𝓑 → 𝓑) (MH : 𝓑) (JH : ℕ)
      → ZCont σ ka A MH JH (kD σ ka) Z (kM σ ka) (kJ σ ka)
ccore ι ka A MH JH =
 λ w → ≤-trans (⊕-increasing-right (pr₁ ka w) (A w ⊕ Z))
        (x-≤-x⊗ (pr₁ ka w ⊕ (A w ⊕ Z)) (bumpk (0 +ℕ JH) (ω ⊕ MH))
          (≤-trans ω-pos
            (≤-trans (⊕-increasing-right ω MH)
                     (≤-bumpk (0 +ℕ JH) (ω ⊕ MH)))))
ccore (σ₁ ⇒ σ₂) (Fa , Da , ca , Ma , ja , gDa , caε , vMa , Maε , zaa)
      A MH JH =
 (pd , pm , pj) , rebased
 where
  Dc : 𝓑 → 𝓑
  Dc = λ w → Da w ⊕ ca

  Mc : 𝓑
  Mc = Ma ⊗ ω

  jc : ℕ
  jc = rbb (σ₁ ⇒ σ₂) ja 0

  pool : 𝓑
  pool = Mc ⊕ MH

  ωpool : ω ≤ pool
  ωpool = ≤-trans (y-≤-⊗ Ma ω (pr₁ vMa)) (⊕-increasing-right Mc MH)

  B+ : (n : ℕ) → S Z ≤ bumpk n pool
  B+ n = ≤-trans (≤-trans ω-pos ωpool) (≤-bumpk n pool)

  pd : (w : 𝓑) → (Da w ⊕ ca)
                  ≤ ((Dc w ⊕ (A w ⊕ Z)) ⊗ bumpk (jc +ℕ JH) pool)
  pd w = ≤-trans (⊕-increasing-right (Dc w) (A w ⊕ Z))
                 (x-≤-x⊗ (Dc w ⊕ (A w ⊕ Z)) (bumpk (jc +ℕ JH) pool)
                         (B+ (jc +ℕ JH)))

  pm : Ma ≤ bumpk (jc +ℕ JH) pool
  pm = ≤-trans (x-≤-x⊗ Ma ω ω-pos)
        (≤-trans (⊕-increasing-right Mc MH) (≤-bumpk (jc +ℕ JH) pool))

  pj : (P : 𝓑) → bumpk ja P ≤ bumpk (jc +ℕ JH) P
  pj P = transport
          (λ n → bumpk ja P ≤ bumpk (n +ℕ JH) P)
          ((rbb-＝ (σ₁ ⇒ σ₂) ja 0) ⁻¹)
          (transport (λ n → bumpk ja P ≤ bumpk n P)
                     ((+ℕ-assoc ja (rbc (σ₁ ⇒ σ₂) 0) JH) ⁻¹)
                     (bumpk-pad ja (rbc (σ₁ ⇒ σ₂) 0 +ℕ JH) P))

  rebased : ZApply σ₁ σ₂ Fa A MH JH Dc Z Mc jc
  rebased = ZApply-rebase σ₁ σ₂ Fa
             (λ _ → Z) A Da Dc Z MH 0 JH ca Z Ma Mc ja ja 0
             I1 I2 I3 I4 zaa
   where
    I1 : (w : 𝓑) → (Da w ⊕ ((λ _ → Z) w ⊕ ca))
         ≤ ((Dc w ⊕ (A w ⊕ Z)) ⊗ bumpk ((ja +ℕ 0) +ℕ JH) pool)
    I1 w = transport
            (λ z → (Da w ⊕ z)
                    ≤ ((Dc w ⊕ (A w ⊕ Z))
                        ⊗ bumpk ((ja +ℕ 0) +ℕ JH) pool))
            ((⊕-Z-left ca) ⁻¹)
            (≤-trans (⊕-increasing-right (Dc w) (A w ⊕ Z))
                     (x-≤-x⊗ (Dc w ⊕ (A w ⊕ Z))
                             (bumpk ((ja +ℕ 0) +ℕ JH) pool)
                             (B+ ((ja +ℕ 0) +ℕ JH))))

    I2 : (Ma ⊕ Z) ≤ bumpk 0 pool
    I2 = ≤-trans (x-≤-x⊗ Ma ω ω-pos) (⊕-increasing-right Mc MH)

    I3 : (P : 𝓑) → bumpk (ja +ℕ 0) P ≤ bumpk (ja +ℕ JH) P
    I3 P = transport (λ n → bumpk n P ≤ bumpk (ja +ℕ JH) P)
                     ((+ℕ-zero-right ja) ⁻¹)
                     (bumpk-pad ja JH P)

    I4 : ω ≤ pool
    I4 = ωpool

cpack : (τ σ : type) (ka : 𝕂 σ) → ZPack τ σ (λ kb → ka)
cpack τ σ ka =
 kD σ ka , Z , kM σ ka , kJ σ ka
 , kD-good σ ka , Z<ε₀ , kM-valid σ ka , kM-ε σ ka
 , body τ
 where
  body : (τ′ : type) → ZApply τ′ σ (λ kb → ka)
                              (λ _ → Z) Z 0 (kD σ ka) Z (kM σ ka) (kJ σ ka)
  body ι         = λ kb → ccore σ ka (λ w → Z ⊕ pr₁ kb w) Z 0
  body (τ₁ ⇒ τ₂) = λ kb → ccore σ ka (λ w → Z ⊕ kadd τ₁ τ₂ kb w)
                                     (Z ⊕ kmult τ₁ τ₂ kb)
                                     (0 +ℕ kbudget τ₁ τ₂ kb)

\end{code}

The outer continuations: the argument under the trivial pack
`(Z , Z , ω , rbb σ 0 0)`, its contributions in the accumulators.

\begin{code}

ocore-ι : (ka : 𝕂 ι) (A : 𝓑 → 𝓑) (MH : 𝓑) (JH J : ℕ)
        → ((w : 𝓑) → pr₁ ka w ≤ A w)
        → ZCont ι ka A MH JH (λ _ → Z) Z ω J
ocore-ι ka A MH JH J hD =
 λ w → ≤-trans (hD w)
        (≤-trans (⊕-increasing-left Z (A w))
                 (x-≤-x⊗ (Z ⊕ (A w ⊕ Z)) (bumpk (J +ℕ JH) (ω ⊕ MH))
                   (≤-trans ω-pos
                     (≤-trans (⊕-increasing-right ω MH)
                              (≤-bumpk (J +ℕ JH) (ω ⊕ MH))))))

ocore-fn : (σ₁ σ₂ : type) (ka : 𝕂 (σ₁ ⇒ σ₂)) (A : 𝓑 → 𝓑) (MH : 𝓑) (JH : ℕ)
         → ((w : 𝓑) → kadd σ₁ σ₂ ka w ≤ A w)
         → (kmult σ₁ σ₂ ka ≤ (ω ⊕ MH))
         → ((P : 𝓑) → bumpk (kbudget σ₁ σ₂ ka) P ≤ bumpk JH P)
         → ZCont (σ₁ ⇒ σ₂) ka A MH JH (λ _ → Z) Z ω (rbb (σ₁ ⇒ σ₂) 0 0)
ocore-fn σ₁ σ₂ (Fa , Da , ca , Ma , ja , gDa , caε , vMa , Maε , zaa)
         A MH JH hD hm hj =
 (pd , pm , pj) , ZApply-rebase σ₁ σ₂ Fa
                   (λ _ → Z) A Da (λ _ → Z) Z MH 0 JH ca Z Ma ω ja 0 0
                   I1 I2 I3 I4 zaa
 where
  pool : 𝓑
  pool = ω ⊕ MH

  B+ : (n : ℕ) → S Z ≤ bumpk n pool
  B+ n = ≤-trans (≤-trans ω-pos (⊕-increasing-right ω MH))
                 (≤-bumpk n pool)

  zchain : (V : 𝓑) (w : 𝓑) (n : ℕ)
         → V ≤ A w → V ≤ ((Z ⊕ (A w ⊕ Z)) ⊗ bumpk n pool)
  zchain V w n h =
   ≤-trans h (≤-trans (⊕-increasing-left Z (A w))
                      (x-≤-x⊗ (Z ⊕ (A w ⊕ Z)) (bumpk n pool) (B+ n)))

  pd : (w : 𝓑) → (Da w ⊕ ca)
       ≤ ((Z ⊕ (A w ⊕ Z)) ⊗ bumpk (rbb (σ₁ ⇒ σ₂) 0 0 +ℕ JH) pool)
  pd w = zchain (Da w ⊕ ca) w (rbb (σ₁ ⇒ σ₂) 0 0 +ℕ JH) (hD w)

  pm : Ma ≤ bumpk (rbb (σ₁ ⇒ σ₂) 0 0 +ℕ JH) pool
  pm = ≤-trans hm (≤-bumpk (rbb (σ₁ ⇒ σ₂) 0 0 +ℕ JH) pool)

  pj : (P : 𝓑) → bumpk ja P ≤ bumpk (rbb (σ₁ ⇒ σ₂) 0 0 +ℕ JH) P
  pj P = ≤-trans (hj P) (bumpk-pad-left (rbb (σ₁ ⇒ σ₂) 0 0) JH P)

  I1 : (w : 𝓑) → (Da w ⊕ ((λ _ → Z) w ⊕ ca))
       ≤ ((Z ⊕ (A w ⊕ Z)) ⊗ bumpk ((0 +ℕ 0) +ℕ JH) pool)
  I1 w = transport
          (λ z → (Da w ⊕ z) ≤ ((Z ⊕ (A w ⊕ Z)) ⊗ bumpk JH pool))
          ((⊕-Z-left ca) ⁻¹)
          (zchain (Da w ⊕ ca) w JH (hD w))

  I2 : (Ma ⊕ Z) ≤ bumpk 0 pool
  I2 = hm

  I3 : (P : 𝓑) → bumpk (ja +ℕ 0) P ≤ bumpk (0 +ℕ JH) P
  I3 P = transport (λ n → bumpk n P ≤ bumpk JH P)
                   ((+ℕ-zero-right ja) ⁻¹) (hj P)

  I4 : ω ≤ pool
  I4 = ⊕-increasing-right ω MH

\end{code}

Consuming and forgetting the `τ`-argument, by cases on `τ`.

\begin{code}

ktail-ι : (τ′ : type) (ka : 𝕂 ι) (A : 𝓑 → 𝓑) (MH : 𝓑) (JH J : ℕ)
        → ((w : 𝓑) → pr₁ ka w ≤ A w)
        → ZApply τ′ ι (λ kb → ka) A MH JH (λ _ → Z) Z ω J
ktail-ι ι ka A MH JH J hD =
 λ kb → ocore-ι ka (λ w → A w ⊕ pr₁ kb w) MH JH J
         (λ w → ≤-trans (hD w) (⊕-increasing-right (A w) (pr₁ kb w)))
ktail-ι (τ₁ ⇒ τ₂) ka A MH JH J hD =
 λ kb → ocore-ι ka (λ w → A w ⊕ kadd τ₁ τ₂ kb w)
         (MH ⊕ kmult τ₁ τ₂ kb) (JH +ℕ kbudget τ₁ τ₂ kb) J
         (λ w → ≤-trans (hD w)
                        (⊕-increasing-right (A w) (kadd τ₁ τ₂ kb w)))

ktail-fn : (τ′ σ₁ σ₂ : type) (ka : 𝕂 (σ₁ ⇒ σ₂))
           (A : 𝓑 → 𝓑) (MH : 𝓑) (JH : ℕ)
         → ((w : 𝓑) → kadd σ₁ σ₂ ka w ≤ A w)
         → (kmult σ₁ σ₂ ka ≤ (ω ⊕ MH))
         → ((P : 𝓑) → bumpk (kbudget σ₁ σ₂ ka) P ≤ bumpk JH P)
         → ZApply τ′ (σ₁ ⇒ σ₂) (λ kb → ka) A MH JH
                  (λ _ → Z) Z ω (rbb (σ₁ ⇒ σ₂) 0 0)
ktail-fn ι σ₁ σ₂ ka A MH JH hD hm hj =
 λ kb → ocore-fn σ₁ σ₂ ka (λ w → A w ⊕ pr₁ kb w) MH JH
         (λ w → ≤-trans (hD w) (⊕-increasing-right (A w) (pr₁ kb w)))
         hm hj
ktail-fn (τ₁ ⇒ τ₂) σ₁ σ₂ ka A MH JH hD hm hj =
 λ kb → ocore-fn σ₁ σ₂ ka (λ w → A w ⊕ kadd τ₁ τ₂ kb w)
         (MH ⊕ kmult τ₁ τ₂ kb) (JH +ℕ kbudget τ₁ τ₂ kb)
         (λ w → ≤-trans (hD w)
                        (⊕-increasing-right (A w) (kadd τ₁ τ₂ kb w)))
         (≤-trans hm (⊕-mono-right ω
                       (⊕-increasing-right MH (kmult τ₁ τ₂ kb))))
         (λ P → ≤-trans (hj P) (bumpk-pad JH (kbudget τ₁ τ₂ kb) P))

\end{code}

The outer pack of `K` itself, by cases on the first argument's type.

\begin{code}

packK : (σ τ : type)
      → ZPack σ (τ ⇒ σ) (λ ka → ((λ kb → ka) , cpack τ σ ka))
packK σ τ =
 (λ _ → Z) , Z , ω , rbb σ 0 0
 , ((λ w _ → Z<ε₀) , (λ w w′ _ → ≤-Z))
 , Z<ε₀ , ω-valid , tower-<-ε₀ 0
 , body σ
 where
  FK : (σ′ : type) → 𝕂 σ′ → 𝕂 (τ ⇒ σ′)
  FK σ′ ka = (λ kb → ka) , cpack τ σ′ ka

  body : (σ′ : type)
       → ZApply σ′ (τ ⇒ σ′) (FK σ′) (λ _ → Z) Z 0
                (λ _ → Z) Z ω (rbb σ′ 0 0)
  body ι = λ ka → (pd ka , pm , pj) , tail ka
   where
    A₁ : 𝕂 ι → 𝓑 → 𝓑
    A₁ ka = λ w → Z ⊕ pr₁ ka w

    pos : (n : ℕ) → S Z ≤ bumpk n (ω ⊕ Z)
    pos n = ≤-trans ω-pos (≤-bumpk n (ω ⊕ Z))

    pd : (ka : 𝕂 ι) (w : 𝓑)
       → (pr₁ ka w ⊕ Z)
         ≤ ((Z ⊕ (A₁ ka w ⊕ Z)) ⊗ bumpk (rbb ι 0 0 +ℕ 0) (ω ⊕ Z))
    pd ka w = ≤-trans (⊕-increasing-left Z (pr₁ ka w))
               (≤-trans (⊕-increasing-left Z (A₁ ka w))
                        (x-≤-x⊗ (Z ⊕ (A₁ ka w ⊕ Z))
                                (bumpk (rbb ι 0 0 +ℕ 0) (ω ⊕ Z))
                                (pos (rbb ι 0 0 +ℕ 0))))

    pm : ω ≤ bumpk (rbb ι 0 0 +ℕ 0) (ω ⊕ Z)
    pm = ≤-bumpk (rbb ι 0 0 +ℕ 0) (ω ⊕ Z)

    pj : (P : 𝓑) → bumpk 0 P ≤ bumpk (rbb ι 0 0 +ℕ 0) P
    pj P = ≤-bumpk (rbb ι 0 0 +ℕ 0) P

    tail : (ka : 𝕂 ι)
         → ZApply τ ι (λ kb → ka) (A₁ ka) Z 0 (λ _ → Z) Z ω (rbb ι 0 0)
    tail ka = ktail-ι τ ka (A₁ ka) Z 0 (rbb ι 0 0)
               (λ w → ⊕-increasing-left Z (pr₁ ka w))
  body (σ₁ ⇒ σ₂) = λ ka →
   (pd ka , pm ka , pj ka) , tail ka
   where
    A₁ : 𝕂 (σ₁ ⇒ σ₂) → 𝓑 → 𝓑
    A₁ ka = λ w → Z ⊕ kadd σ₁ σ₂ ka w

    MH₁ : 𝕂 (σ₁ ⇒ σ₂) → 𝓑
    MH₁ ka = Z ⊕ kmult σ₁ σ₂ ka

    pool₁ : 𝕂 (σ₁ ⇒ σ₂) → 𝓑
    pool₁ ka = ω ⊕ MH₁ ka

    hDin : (ka : 𝕂 (σ₁ ⇒ σ₂)) (w : 𝓑) → kadd σ₁ σ₂ ka w ≤ A₁ ka w
    hDin ka w = ⊕-increasing-left Z (kadd σ₁ σ₂ ka w)

    hmin : (ka : 𝕂 (σ₁ ⇒ σ₂)) → kmult σ₁ σ₂ ka ≤ pool₁ ka
    hmin ka = ≤-trans (⊕-increasing-left Z (kmult σ₁ σ₂ ka))
                      (⊕-increasing-left ω (MH₁ ka))

    pos₁ : (ka : 𝕂 (σ₁ ⇒ σ₂)) (n : ℕ) → S Z ≤ bumpk n (pool₁ ka)
    pos₁ ka n = ≤-trans (≤-trans ω-pos (⊕-increasing-right ω (MH₁ ka)))
                        (≤-bumpk n (pool₁ ka))

    pd : (ka : 𝕂 (σ₁ ⇒ σ₂)) (w : 𝓑)
       → (kD (σ₁ ⇒ σ₂) ka w ⊕ Z)
         ≤ ((Z ⊕ (A₁ ka w ⊕ Z))
             ⊗ bumpk (rbb (σ₁ ⇒ σ₂) 0 0 +ℕ (0 +ℕ kbudget σ₁ σ₂ ka))
                     (pool₁ ka))
    pd ka w = ≤-trans (hDin ka w)
               (≤-trans (⊕-increasing-left Z (A₁ ka w))
                        (x-≤-x⊗ (Z ⊕ (A₁ ka w ⊕ Z))
                                (bumpk (rbb (σ₁ ⇒ σ₂) 0 0
                                        +ℕ (0 +ℕ kbudget σ₁ σ₂ ka))
                                       (pool₁ ka))
                                (pos₁ ka (rbb (σ₁ ⇒ σ₂) 0 0
                                          +ℕ (0 +ℕ kbudget σ₁ σ₂ ka)))))

    pm : (ka : 𝕂 (σ₁ ⇒ σ₂))
       → kM (σ₁ ⇒ σ₂) ka
         ≤ bumpk (rbb (σ₁ ⇒ σ₂) 0 0 +ℕ (0 +ℕ kbudget σ₁ σ₂ ka))
                 (pool₁ ka)
    pm ka =
     ≤-trans
      (≤-trans (⊗-mono-left (hmin ka) ω)
        (≤-trans (⊗-mono-right (pool₁ ka)
                   (⊕-increasing-right ω (MH₁ ka)))
                 (⊗-≤-bump (pool₁ ka))))
      (transport (λ n → bumpk 1 (pool₁ ka)
                         ≤ bumpk (n +ℕ kbudget σ₁ σ₂ ka) (pool₁ ka))
                 ((pr₂ spl) ⁻¹)
                 (bumpk-pad-left-succ ka))
     where
      spl : Σ d ꞉ ℕ , rbb (σ₁ ⇒ σ₂) 0 0 ＝ (succ (0 +ℕ 0) +ℕ d)
      spl = rbb-split (σ₁ ⇒ σ₂) 0 0

      bumpk-pad-left-succ : (ka′ : 𝕂 (σ₁ ⇒ σ₂))
        → bumpk 1 (pool₁ ka′)
          ≤ bumpk ((succ (0 +ℕ 0) +ℕ pr₁ spl) +ℕ kbudget σ₁ σ₂ ka′)
                  (pool₁ ka′)
      bumpk-pad-left-succ ka′ =
       transport (λ n → bumpk 1 (pool₁ ka′) ≤ bumpk n (pool₁ ka′))
                 (+ℕ-assoc 1 (pr₁ spl) (kbudget σ₁ σ₂ ka′) ⁻¹ ∙ refl)
                 (bumpk-pad 1 (pr₁ spl +ℕ kbudget σ₁ σ₂ ka′) (pool₁ ka′))

    pj : (ka : 𝕂 (σ₁ ⇒ σ₂)) (P : 𝓑)
       → bumpk (kJ (σ₁ ⇒ σ₂) ka) P
         ≤ bumpk (rbb (σ₁ ⇒ σ₂) 0 0 +ℕ (0 +ℕ kbudget σ₁ σ₂ ka)) P
    pj ka P =
     transport (λ n → bumpk (rbb (σ₁ ⇒ σ₂) (kbudget σ₁ σ₂ ka) 0) P
                       ≤ bumpk n P)
               E
               (≤-refl (bumpk (rbb (σ₁ ⇒ σ₂) (kbudget σ₁ σ₂ ka) 0) P))
     where
      ja′ : ℕ
      ja′ = kbudget σ₁ σ₂ ka

      E : rbb (σ₁ ⇒ σ₂) ja′ 0 ＝ (rbb (σ₁ ⇒ σ₂) 0 0 +ℕ ja′)
      E = rbb-＝ (σ₁ ⇒ σ₂) ja′ 0
          ∙ +ℕ-comm ja′ (rbc (σ₁ ⇒ σ₂) 0)
          ∙ (ap (_+ℕ ja′) (rbb-＝ (σ₁ ⇒ σ₂) 0 0)) ⁻¹

    tail : (ka : 𝕂 (σ₁ ⇒ σ₂))
         → ZApply τ (σ₁ ⇒ σ₂) (λ kb → ka) (A₁ ka) (MH₁ ka)
                  (0 +ℕ kbudget σ₁ σ₂ ka)
                  (λ _ → Z) Z ω (rbb (σ₁ ⇒ σ₂) 0 0)
    tail ka = ktail-fn τ σ₁ σ₂ ka (A₁ ka) (MH₁ ka)
               (0 +ℕ kbudget σ₁ σ₂ ka)
               (hDin ka) (hmin ka)
               (λ P → ≤-refl (bumpk (kbudget σ₁ σ₂ ka) P))

\end{code}

The combinator, assembled.

\begin{code}

GoodH-K : {σ τ : type} → GoodH (σ ⇒ τ ⇒ σ) μ-K
GoodH-K {σ} {τ} =
 (λ Ta Tb → Ta)
 , (maps , (((λ ka → ((λ kb → ka) , cpack τ σ ka)) , packK σ τ)
           , (λ a ka bnda b kb bndb → bnda)))
 , (λ w a Ta lTa a-glob b Tb lTb b-glob → a-glob w)
 where
  maps : (Ta : 𝕋 σ) → LT σ Ta → LT (τ ⇒ σ) (λ Tb → Ta)
  maps Ta lTa =
   (λ Tb lTb → lTa)
   , (((λ kb → pr₁ r) , cpack τ σ (pr₁ r))
     , (λ b kb bndb → pr₂ r))
   where
    r : Σ k ꞉ 𝕂 σ , BndH σ Ta k
    r = reflect σ Ta lTa

\end{code}
