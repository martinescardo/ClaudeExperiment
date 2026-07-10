Design H, stage 2d(x-b): the `S`-diagonal pack at a *function-typed* middle
`σ = σ₁ ⇒ σ₂` — the case Design F cannot reach, the Howard tower's purpose.

At a ground middle (`MultHereditaryH8`) the γ-value fed to `φ`'s slot is a
`GFun`, bounded directly. At a function middle it is a `𝕂 (σ₁ ⇒ σ₂)`, fed
via the `ZApply` *arrow* clause, and its additive/multiplier/budget data
enter the diagonal's accumulators — bounded by **γ's own `PackDom`** (the
tower predicate's constraining clause, `MultHereditaryH.PackDom`), which is
exactly what supplies the three rebase hypotheses:

* `I1` (additive): `kadd`γ is bounded by `⊗ Bγ` (γ's `PackDom` additive
  clause) — the same shape as the ground γ-value, so `I1` reuses the ground
  `quad4` + `diag-absorb`;
* `I2` (multiplier): `kmult`γ ≤ `bumpk jγ Mγ` (γ's `PackDom` multiplier
  clause), absorbed by `MultHereditaryH16.fnmid-I2`;
* `I3` (budget): `kbudget`γ dominated by `jγ` (γ's `PackDom` budget clause),
  threaded through `bumpk-+`.

The budget routing matters, but does not — on its own — close the composition
into `pack2`. γ contributes `jγ` *twice*: via its budget (into
`uδ = jφ +ℕ jγ`, hence `jδ`) and via its multiplier (`kmult`γ, absorbed by
`fnmid-I2`). We route the multiplier's `jγ` into `Mδ` rather than into rebase
slack: keep `eδ = 2` and set `Mδ = bumpk (jγ +ℕ 3) (Mφ ⊗ (Mγ ⊗ ω))`. Since
`M′ ⊕ MH′` reduces to `Mδ` at the rebase target (`_⊕ Z` is definitional),
`fnmid-I2`'s output index (total `jγ +ℕ 5` over the base) re-splits as
`eδ = 2` slack plus a `bumpk (jγ +ℕ 3)` multiplier — *the same lemma,
regrouped*. The payoff is that `jδ = rbb τ (jφ +ℕ jγ) 2` carries `jγ`
*once* (`rbb`'s overhead over `u` is `u`-free), so the **scalar** `PackDom`
clauses of `pack2` — multiplier `Mδ ≤ bumpk (j2 +ℕ jγ) pool` (via
`bumpk jγ`-lifted `mult-absorb`) and budget `jδ ≤ j2 +ℕ jγ` — both compose.

But the composition still fails at one spot, and it is *structural*, not a
matter of rebase plumbing. The diagonal's ground **leaf** multiplier is
`bumpk (jδ) Mδ = bumpk (jφ +ℕ 2·jγ +ℕ 6) base₀` — carrying `jγ` **twice**,
because feeding the function-value `γ a` to `φ` charges *both* its budget
(into `JH`) and its multiplier `≤ bumpk jγ Mγ` (into `MH`), and the flat pool
`bumpk (j +ℕ JH) (M ⊕ MH)` composes the two multiplicatively. `pack2`'s
target leaf is `bumpk (j2 +ℕ jγ) pool` with `j2` necessarily `jγ`-free — only
**one** `jγ`. No choice of `Mδ`/`eδ`/`j2`, and no strengthening of the rebase
`I2`, can manufacture the second `jγ` the target does not carry. This
`2·jγ`-vs-`1·jγ` leaf deficit is the genuine ordinal cost of feeding a
budget-bumped function-value — the essential difficulty the flat-pool tower
predicate cannot express, and close to the heart of the open conjecture. This
module builds `packδ` for the function-middle case, any `σ₁ σ₂ τ`, verified
*in isolation* with the composition-ready scalar routing; the fn-middle
theorem awaits a predicate that folds each argument's budget into its own
pool contribution. The conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryH17
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe
 using (ω ; _⊗_ ; ⊕-mono-left ; ⊕-assoc)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right ;
        ⊕-increasing-right ; ⊕-<-ε₀ ; tower-<-ε₀)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊗-assoc ; ⊕-increasing-left)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (⊗-<-ε₀)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (x-≤-x⊗ ; y-≤-⊗ ; Z<ε₀)
open import Claude.BrouwerOrdinals.MultAffine fe using (ω-pos)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; ω-valid ; validMult-⊗)
open import Claude.DialogueTreeHeight.MultHereditaryF fe
 using (GoodT ; GoodT-⊕)
open import Claude.BrouwerOrdinals.MultBump fe
 using (bump ; bumpk ; bumpk-mono ; ≤-bump ; bumpk-valid ; bumpk-<-ε₀)
open import Claude.DialogueTreeHeight.MultHereditaryG fe using (GFun)
open import Claude.DialogueTreeHeight.MultHereditaryH fe
 using (_+ℕ_ ; 𝕂 ; ZPack ; ZApply ; ZCont ; PackDom ;
        kadd ; kmult ; kbudget)
open import Claude.DialogueTreeHeight.MultHereditaryH2 fe
 using (+ℕ-zero-right ; +ℕ-comm ; +ℕ-assoc ; bumpk-+ ; ≤-bumpk ; rbb)
open import Claude.DialogueTreeHeight.MultHereditaryH3 fe
 using (ZCont-rebase)
open import Claude.DialogueTreeHeight.MultHereditaryH4 fe
 using (⊕-Z-left)
open import Claude.DialogueTreeHeight.MultHereditaryH10 fe
 using (le ; bumpk-le ; le-refl ; le-trans ; le-add-right ; le-add-left ;
        le-＝-left ; le-＝-right)
open import Claude.DialogueTreeHeight.MultHereditaryH8 fe
 using (trip3r ; quad4)
open import Claude.DialogueTreeHeight.MultHereditaryH11 fe
 using (diag-absorb)
open import Claude.DialogueTreeHeight.MultHereditaryH16 fe
 using (fnmid-I2)

\end{code}

The function-middle diagonal pack.

\begin{code}

module Sδ-fnmid
 (σ₁ σ₂ τ : type)
 (kφ : 𝕂 (ι ⇒ ((σ₁ ⇒ σ₂) ⇒ τ)))
 (kγ : 𝕂 (ι ⇒ (σ₁ ⇒ σ₂)))
 where

 Fφ : GFun → 𝕂 ((σ₁ ⇒ σ₂) ⇒ τ)
 Fφ = pr₁ kφ
 Dφ : 𝓑 → 𝓑
 Dφ = pr₁ (pr₂ kφ)
 cφ Mφ : 𝓑
 cφ = pr₁ (pr₂ (pr₂ kφ))
 Mφ = pr₁ (pr₂ (pr₂ (pr₂ kφ)))
 jφ : ℕ
 jφ = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ kφ))))
 gDφ : GoodT ι Dφ
 gDφ = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ kφ)))))
 cφε : cφ < ε₀
 cφε = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ kφ))))))
 vMφ : ValidMult Mφ
 vMφ = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ kφ)))))))
 Mφε : Mφ < ε₀
 Mφε = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ kφ))))))))
 zaφ : ZApply ι ((σ₁ ⇒ σ₂) ⇒ τ) Fφ (λ _ → Z) Z 0 Dφ cφ Mφ jφ
 zaφ = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ kφ))))))))

 Fγ : GFun → 𝕂 (σ₁ ⇒ σ₂)
 Fγ = pr₁ kγ
 Dγ : 𝓑 → 𝓑
 Dγ = pr₁ (pr₂ kγ)
 cγ Mγ : 𝓑
 cγ = pr₁ (pr₂ (pr₂ kγ))
 Mγ = pr₁ (pr₂ (pr₂ (pr₂ kγ)))
 jγ : ℕ
 jγ = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ kγ))))
 gDγ : GoodT ι Dγ
 gDγ = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ kγ)))))
 cγε : cγ < ε₀
 cγε = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ kγ))))))
 vMγ : ValidMult Mγ
 vMγ = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ kγ)))))))
 Mγε : Mγ < ε₀
 Mγε = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ kγ))))))))
 zaγ : ZApply ι (σ₁ ⇒ σ₂) Fγ (λ _ → Z) Z 0 Dγ cγ Mγ jγ
 zaγ = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ kγ))))))))

 Bγ : 𝓑
 Bγ = bumpk (jγ +ℕ 0) (Mγ ⊕ Z)
 Bγ+ : S Z ≤ Bγ
 Bγ+ = pr₁ (bumpk-valid (jγ +ℕ 0) vMγ)
 vωBγ : S Z ≤ (ω ⊗ Bγ)
 vωBγ = ≤-trans ω-pos (x-≤-x⊗ ω Bγ Bγ+)

 base₀ : 𝓑
 base₀ = Mφ ⊗ (Mγ ⊗ ω)
 vbase₀ : ValidMult base₀
 vbase₀ = validMult-⊗ vMφ (validMult-⊗ vMγ ω-valid)
 base₀ε : base₀ < ε₀
 base₀ε = ⊗-<-ε₀ Mφ (Mγ ⊗ ω) Mφε (⊗-<-ε₀ Mγ ω Mγε (tower-<-ε₀ 0))

 Mδ : 𝓑
 Mδ = bumpk (jγ +ℕ 3) base₀
 vMδ : ValidMult Mδ
 vMδ = bumpk-valid (jγ +ℕ 3) vbase₀
 Mδε : Mδ < ε₀
 Mδε = bumpk-<-ε₀ (jγ +ℕ 3) base₀ε

 Dδ : 𝓑 → 𝓑
 Dδ = λ w → Dφ w ⊕ Dγ w
 gDδ : GoodT ι Dδ
 gDδ = GoodT-⊕ Dφ Dγ gDφ gDγ
 cδ : 𝓑
 cδ = cγ ⊕ cφ
 cδε : cδ < ε₀
 cδε = ⊕-<-ε₀ cγ cφ cγε cφε

 uδ eδ : ℕ
 uδ = jφ +ℕ jγ
 eδ = 2
 jδ : ℕ
 jδ = rbb τ uδ eδ

 Fδ : GFun → 𝕂 τ
 Fδ ka = pr₁ (Fφ ka) (Fγ ka)

 vMγω : S Z ≤ (Mγ ⊗ ω)
 vMγω = ≤-trans ω-pos (y-≤-⊗ Mγ ω (pr₁ vMγ))
 Mφ≤base₀ : Mφ ≤ base₀
 Mφ≤base₀ = x-≤-x⊗ Mφ (Mγ ⊗ ω) vMγω
 ω≤base₀ : ω ≤ base₀
 ω≤base₀ = ≤-trans (y-≤-⊗ Mγ ω (pr₁ vMγ)) (y-≤-⊗ Mφ (Mγ ⊗ ω) (pr₁ vMφ))
 Mφ≤Mδ : Mφ ≤ Mδ
 Mφ≤Mδ = ≤-trans Mφ≤base₀ (≤-bumpk (jγ +ℕ 3) base₀)
 ω≤Mδ : ω ≤ Mδ
 ω≤Mδ = ≤-trans ω≤base₀ (≤-bumpk (jγ +ℕ 3) base₀)

 -- keyM : the I1 finish bound, via diag-absorb at the enlarged index.
 -- The multiplier now carries jγ (Mδ = bumpk (jγ +ℕ 3) base₀), so the
 -- inner constant is (jγ +ℕ 3), not 3; the total index is unchanged.
 leKM : le (2 +ℕ (jγ +ℕ 0)) (((uδ +ℕ eδ) +ℕ 0) +ℕ (jγ +ℕ 3))
 leKM = (uδ +ℕ 3) , eqKM
  where
   eqKM : (((uδ +ℕ eδ) +ℕ 0) +ℕ (jγ +ℕ 3))
          ＝ ((2 +ℕ (jγ +ℕ 0)) +ℕ (uδ +ℕ 3))
   eqKM = lhsNF ∙ rhsNF ⁻¹
    where
     lhsNF : (((uδ +ℕ eδ) +ℕ 0) +ℕ (jγ +ℕ 3)) ＝ (uδ +ℕ (jγ +ℕ 5))
     lhsNF = ap (_+ℕ (jγ +ℕ 3)) (+ℕ-zero-right (uδ +ℕ eδ))
             ∙ +ℕ-assoc uδ 2 (jγ +ℕ 3)
             ∙ ap (uδ +ℕ_) (+ℕ-comm 2 (jγ +ℕ 3) ∙ +ℕ-assoc jγ 3 2)
     rhsNF : ((2 +ℕ (jγ +ℕ 0)) +ℕ (uδ +ℕ 3)) ＝ (uδ +ℕ (jγ +ℕ 5))
     rhsNF = ap (λ z → (2 +ℕ z) +ℕ (uδ +ℕ 3)) (+ℕ-zero-right jγ)
             ∙ +ℕ-comm (2 +ℕ jγ) (uδ +ℕ 3)
             ∙ +ℕ-assoc uδ 3 (2 +ℕ jγ)
             ∙ ap (uδ +ℕ_) ((+ℕ-assoc 3 2 jγ) ⁻¹ ∙ +ℕ-comm 5 jγ)

 keyM : ((ω ⊗ Bγ) ⊗ ω) ≤ bumpk ((uδ +ℕ eδ) +ℕ 0) (Mδ ⊕ Z)
 keyM = ≤-trans (diag-absorb Mφ Mγ (jγ +ℕ 0) (pr₁ vMφ) (pr₁ vMγ))
          (transport (λ z → bumpk (2 +ℕ (jγ +ℕ 0)) base₀ ≤ z)
                     (bumpk-+ ((uδ +ℕ eδ) +ℕ 0) (jγ +ℕ 3) base₀)
                     (bumpk-le base₀ leKM))

\end{code}

The diagonal `ZCont`, per shared argument, using γ's `PackDom`.

\begin{code}

 packδ-body : (ka : GFun)
            → ZCont τ (Fδ ka) (λ w → Z ⊕ pr₁ ka w) Z 0 Dδ cδ Mδ jδ
 packδ-body ka =
  ZCont-rebase τ (Fδ ka)
    Asrc accₐ Dφ Dδ (Z ⊕ kmult σ₁ σ₂ kg) Z
    (0 +ℕ kbudget σ₁ σ₂ kg) 0 cφ cδ Mφ Mδ jφ uδ eδ
    I1 I2 I3 ω≤Mδ (zaφ2 kg)
  where
   accₐ : 𝓑 → 𝓑
   accₐ = λ w → Z ⊕ pr₁ ka w

   kg : 𝕂 (σ₁ ⇒ σ₂)
   kg = Fγ ka

   Asrc : 𝓑 → 𝓑
   Asrc = λ w → accₐ w ⊕ kadd σ₁ σ₂ kg w

   zaφ2 : (kh : 𝕂 (σ₁ ⇒ σ₂))
        → ZCont τ (pr₁ (Fφ ka) kh)
                (λ w → accₐ w ⊕ kadd σ₁ σ₂ kh w)
                (Z ⊕ kmult σ₁ σ₂ kh) (0 +ℕ kbudget σ₁ σ₂ kh)
                Dφ cφ Mφ jφ
   zaφ2 = pr₂ (zaφ ka)

   pdγ : (w : 𝓑) → kadd σ₁ σ₂ kg w
                    ≤ ((Dγ w ⊕ (accₐ w ⊕ cγ)) ⊗ Bγ)
   pdγ = pr₁ (pr₁ (zaγ ka))
   pmγ : kmult σ₁ σ₂ kg ≤ Bγ
   pmγ = pr₁ (pr₂ (pr₁ (zaγ ka)))
   pjγ : (P : 𝓑) → bumpk (kbudget σ₁ σ₂ kg) P ≤ bumpk (jγ +ℕ 0) P
   pjγ = pr₂ (pr₂ (pr₁ (zaγ ka)))

   I3 : (P : 𝓑)
      → bumpk (jφ +ℕ (0 +ℕ kbudget σ₁ σ₂ kg)) P ≤ bumpk (uδ +ℕ 0) P
   I3 P =
    transport (λ n → bumpk (jφ +ℕ (0 +ℕ kbudget σ₁ σ₂ kg)) P ≤ bumpk n P)
              ((+ℕ-zero-right uδ) ⁻¹)
              (≤-trans s3 (bumpk-le P leI3))
    where
     kb : ℕ
     kb = kbudget σ₁ σ₂ kg
     s2 : bumpk jφ (bumpk kb P) ≤ bumpk jφ (bumpk (jγ +ℕ 0) P)
     s2 = bumpk-mono jφ (pjγ P)
     s3 : bumpk (jφ +ℕ kb) P ≤ bumpk (jφ +ℕ (jγ +ℕ 0)) P
     s3 = transport (λ x → bumpk (jφ +ℕ kb) P ≤ x)
                    ((bumpk-+ jφ (jγ +ℕ 0) P) ⁻¹)
            (transport (λ x → x ≤ bumpk jφ (bumpk (jγ +ℕ 0) P))
                       ((bumpk-+ jφ kb P) ⁻¹) s2)
     leI3 : le (jφ +ℕ (jγ +ℕ 0)) uδ
     leI3 = le-＝-left (ap (jφ +ℕ_) (+ℕ-zero-right jγ)) (le-refl uδ)

   -- fnmid-I2 lands at bumpk ((jγ +ℕ 0) +ℕ 2) (bumpk 3 base₀), total index
   -- jγ +ℕ 5 over base₀; regroup as bumpk eδ (bumpk (jγ +ℕ 3) base₀) =
   -- bumpk eδ (Mδ ⊕ Z), keeping eδ = 2 constant.
   I2 : (Mφ ⊕ (Z ⊕ kmult σ₁ σ₂ kg)) ≤ bumpk eδ (Mδ ⊕ Z)
   I2 =
    transport (λ z → (Mφ ⊕ z) ≤ bumpk eδ (Mδ ⊕ Z))
              ((⊕-Z-left (kmult σ₁ σ₂ kg)) ⁻¹)
      (transport (λ K → (Mφ ⊕ kmult σ₁ σ₂ kg) ≤ K) eqbase
        (fnmid-I2 Mφ Mγ (kmult σ₁ σ₂ kg) (jγ +ℕ 0)
                  (pr₁ vMφ) (pr₁ vMγ) pmγ))
    where
     eqbase : bumpk ((jγ +ℕ 0) +ℕ 2) (bumpk 3 base₀) ＝ bumpk eδ (Mδ ⊕ Z)
     eqbase = (bumpk-+ ((jγ +ℕ 0) +ℕ 2) 3 base₀) ⁻¹
              ∙ ap (λ n → bumpk n base₀) eqIdx
              ∙ bumpk-+ eδ (jγ +ℕ 3) base₀
      where
       eqIdx : (((jγ +ℕ 0) +ℕ 2) +ℕ 3) ＝ (eδ +ℕ (jγ +ℕ 3))
       eqIdx = (ap (λ z → (z +ℕ 2) +ℕ 3) (+ℕ-zero-right jγ)
                ∙ +ℕ-assoc jγ 2 3)
               ∙ (+ℕ-comm 2 (jγ +ℕ 3) ∙ +ℕ-assoc jγ 3 2) ⁻¹

   I1 : (w : 𝓑) → (Dφ w ⊕ (Asrc w ⊕ cφ))
        ≤ ((Dδ w ⊕ (accₐ w ⊕ cδ)) ⊗ bumpk ((uδ +ℕ eδ) +ℕ 0) (Mδ ⊕ Z))
   I1 w = transport
           (λ z → z ≤ ((Dδ w ⊕ (accₐ w ⊕ cδ))
                        ⊗ bumpk ((uδ +ℕ eδ) +ℕ 0) (Mδ ⊕ Z)))
           (reassoc ⁻¹)
           (≤-trans quad finish)
    where
     X : 𝓑
     X = kadd σ₁ σ₂ kg w
     Y : 𝓑
     Y = Dδ w ⊕ (accₐ w ⊕ cδ)
     Q : 𝓑
     Q = Y ⊗ (ω ⊗ Bγ)
     Dφ≤Y : Dφ w ≤ Y
     Dφ≤Y = ≤-trans (⊕-increasing-right (Dφ w) (Dγ w))
                    (⊕-increasing-right (Dδ w) (accₐ w ⊕ cδ))
     accₐ≤Y : accₐ w ≤ Y
     accₐ≤Y = ≤-trans (⊕-increasing-right (accₐ w) cδ)
                      (⊕-increasing-left (Dδ w) (accₐ w ⊕ cδ))
     cφ≤Y : cφ ≤ Y
     cφ≤Y = ≤-trans (⊕-increasing-left cγ cφ)
              (≤-trans (⊕-increasing-left (accₐ w) cδ)
                       (⊕-increasing-left (Dδ w) (accₐ w ⊕ cδ)))
     Dγ≤Y : Dγ w ≤ Y
     Dγ≤Y = ≤-trans (⊕-increasing-left (Dφ w) (Dγ w))
                    (⊕-increasing-right (Dδ w) (accₐ w ⊕ cδ))
     cγ≤Y : cγ ≤ Y
     cγ≤Y = ≤-trans (⊕-increasing-right cγ cφ)
              (≤-trans (⊕-increasing-left (accₐ w) cδ)
                       (⊕-increasing-left (Dδ w) (accₐ w ⊕ cδ)))
     Y≤Q : Y ≤ Q
     Y≤Q = x-≤-x⊗ Y (ω ⊗ Bγ) vωBγ
     X≤Q : X ≤ Q
     X≤Q = ≤-trans (pdγ w)
            (transport (λ z → ((Dγ w ⊕ (accₐ w ⊕ cγ)) ⊗ Bγ) ≤ z)
                       (⊗-assoc Y ω Bγ)
                       (⊗-mono-left
                         (trip3r (Dγ w) (accₐ w) cγ Y Dγ≤Y accₐ≤Y cγ≤Y)
                         Bγ))
     reassoc : (Dφ w ⊕ (Asrc w ⊕ cφ)) ＝ (Dφ w ⊕ (accₐ w ⊕ (X ⊕ cφ)))
     reassoc = ap (λ z → Dφ w ⊕ z) (⊕-assoc (accₐ w) X cφ)
     quad : (Dφ w ⊕ (accₐ w ⊕ (X ⊕ cφ))) ≤ (Q ⊗ ω)
     quad = quad4 (Dφ w) (accₐ w) X cφ Q
              (≤-trans Dφ≤Y Y≤Q) (≤-trans accₐ≤Y Y≤Q) X≤Q (≤-trans cφ≤Y Y≤Q)
     finish : (Q ⊗ ω) ≤ (Y ⊗ bumpk ((uδ +ℕ eδ) +ℕ 0) (Mδ ⊕ Z))
     finish = transport (λ z → z ≤ (Y ⊗ bumpk ((uδ +ℕ eδ) +ℕ 0) (Mδ ⊕ Z)))
                        ((⊗-assoc Y (ω ⊗ Bγ) ω) ⁻¹)
                        (⊗-mono-right Y keyM)

 packδ : ZPack ι τ Fδ
 packδ = Dδ , cδ , Mδ , jδ , gDδ , cδε , vMδ , Mδε , packδ-body

\end{code}
