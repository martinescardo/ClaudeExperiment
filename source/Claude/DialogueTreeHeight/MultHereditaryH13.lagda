Design H, stage 2d(viii-b): `pack2` — the middle pack of the `S` combinator
over the Howard tower (`ρ = σ = τ = ι`), assembled.

Consuming the second argument `kγ`, `pack2` produces the zone pack of the
jγ-free diagonal `kδ = (Fδ , packδ)` (`MultHereditaryH8`). The `PackDom`
obligations thread the verified arithmetic (`MultHereditaryH12` `L-pm`/
`L-pj`, `MultHereditaryH9.mult-absorb` at `n = 0`) with quadruple zone
absorption; the inner `ZApply` rebases `packδ`'s body by one `ZCont-rebase`
at the **constant** slack `e = 5` (the payoff of the jγ-free multiplier),
its invariants discharged by `L-I3z`/`L-I1z`/`mult-absorb` and a five-fold
absorption. The output budget is `j₂ = rbb ι (3 +ℕ jφ) 5` (matching the
rebase output definitionally); `MultHereditaryH12.eq-j2` converts it to
`9 +ℕ jφ` where the `PackDom` lemmas are stated. The conjecture remains
open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryH13
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
        ⊕-increasing-right ; tower-<-ε₀)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊗-assoc ; ⊕-increasing-left)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (⊗-<-ε₀)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (x-≤-x⊗ ; y-≤-⊗)
open import Claude.BrouwerOrdinals.MultAffine fe using (ω-pos)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; ω-valid ; validMult-⊗)
open import Claude.DialogueTreeHeight.MultHereditaryF fe
 using (GoodT)
open import Claude.DialogueTreeHeight.MultHereditaryFAff fe
 using (⊕-dup-≤-⊗ω)
open import Claude.BrouwerOrdinals.MultBump fe
 using (bump ; bumpk ; ≤-bump ; ⊗-≤-bump)
open import Claude.DialogueTreeHeight.MultHereditaryG fe using (GFun)
open import Claude.DialogueTreeHeight.MultHereditaryH fe
 using (_+ℕ_ ; 𝕂 ; ZPack ; ZApply ; ZCont ; PackDom ;
        kadd ; kmult ; kbudget)
open import Claude.DialogueTreeHeight.MultHereditaryH2 fe
 using (bumpk-+ ; ≤-bumpk ; rbb)
open import Claude.DialogueTreeHeight.MultHereditaryH3 fe
 using (ZCont-rebase)
open import Claude.DialogueTreeHeight.MultHereditaryH4 fe
 using (⊕-Z-left)
open import Claude.DialogueTreeHeight.MultHereditaryH9 fe
 using (mult-absorb)
open import Claude.DialogueTreeHeight.MultHereditaryH10 fe
 using (le ; bumpk-le ; le-＝-right)
open import Claude.DialogueTreeHeight.MultHereditaryH8 fe
 using (quad4 ; module Sδ-ground)
open import Claude.DialogueTreeHeight.MultHereditaryH12 fe
 using (eq-j2 ; L-pm ; L-pj ; L-I3z ; L-I1z)

\end{code}

Five-fold absorption: five summands each below `Y` sit below `Y ⊗ (ω ⊗ ω)`
(a quadruple absorption of the last four, then one duplication for the
fifth).

\begin{code}

pent5 : (a b c d e Y : 𝓑) → a ≤ Y → b ≤ Y → c ≤ Y → d ≤ Y → e ≤ Y
      → (a ⊕ (b ⊕ (c ⊕ (d ⊕ e)))) ≤ (Y ⊗ (ω ⊗ ω))
pent5 a b c d e Y ha hb hc hd he =
 transport (λ z → (a ⊕ (b ⊕ (c ⊕ (d ⊕ e)))) ≤ z) (⊗-assoc Y ω ω)
   (≤-trans (⊕-mono-left ha (b ⊕ (c ⊕ (d ⊕ e))))
     (≤-trans (⊕-mono-right Y (quad4 b c d e Y hb hc hd he))
       (≤-trans (⊕-mono-left (x-≤-x⊗ Y ω ω-pos) (Y ⊗ ω))
                (⊕-dup-≤-⊗ω (Y ⊗ ω)))))

\end{code}

The middle pack, parameterized by the first argument.

\begin{code}

module Spack2 (kφ : 𝕂 (ι ⇒ ι ⇒ ι)) where

 Dφ0 : 𝓑 → 𝓑
 Dφ0 = pr₁ (pr₂ kφ)
 cφ0 Mφ0 : 𝓑
 cφ0 = pr₁ (pr₂ (pr₂ kφ))
 Mφ0 = pr₁ (pr₂ (pr₂ (pr₂ kφ)))
 jφ0 : ℕ
 jφ0 = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ kφ))))
 gDφ0 : GoodT ι Dφ0
 gDφ0 = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ kφ)))))
 cφε0 : cφ0 < ε₀
 cφε0 = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ kφ))))))
 vMφ0 : ValidMult Mφ0
 vMφ0 = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ kφ)))))))
 Mφε0 : Mφ0 < ε₀
 Mφε0 = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ kφ))))))))

 F2 : 𝕂 (ι ⇒ ι) → 𝕂 (ι ⇒ ι)
 F2 kγ = Sδ-ground.Fδ ι kφ kγ , Sδ-ground.packδ ι kφ kγ

 D2 : 𝓑 → 𝓑
 D2 = Dφ0
 M2 : 𝓑
 M2 = Mφ0 ⊗ ω
 ur : ℕ
 ur = 3 +ℕ jφ0
 j2 : ℕ
 j2 = rbb ι ur 5

 vM2 : ValidMult M2
 vM2 = validMult-⊗ vMφ0 ω-valid
 M2ε : M2 < ε₀
 M2ε = ⊗-<-ε₀ Mφ0 ω Mφε0 (tower-<-ε₀ 0)

 pack2 : ZPack (ι ⇒ ι) (ι ⇒ ι) F2
 pack2 = D2 , cφ0 , M2 , j2 , gDφ0 , cφε0 , vM2 , M2ε , body
  where
   body : (kγ : 𝕂 (ι ⇒ ι))
        → ZCont (ι ⇒ ι) (F2 kγ)
                (λ w → Z ⊕ kadd ι ι kγ w) (Z ⊕ kmult ι ι kγ)
                (0 +ℕ kbudget ι ι kγ) D2 cφ0 M2 j2
   body kγ = (pd , pm , pj) , za
    where
     open Sδ-ground ι kφ kγ

     acc : 𝓑 → 𝓑
     acc = λ w → Z ⊕ (Dγ w ⊕ cγ)
     MH : 𝓑
     MH = Z ⊕ Mγ
     pool : 𝓑
     pool = M2 ⊕ MH

     hφ : Mφ0 ≤ pool
     hφ = ≤-trans (x-≤-x⊗ Mφ0 ω ω-pos) (⊕-increasing-right M2 MH)
     hγ : Mγ ≤ pool
     hγ = ≤-trans (⊕-increasing-left Z Mγ) (⊕-increasing-left M2 MH)
     hω : ω ≤ pool
     hω = ≤-trans (y-≤-⊗ Mφ0 ω (pr₁ vMφ0)) (⊕-increasing-right M2 MH)

     ω≤bump : (n : ℕ) → ω ≤ bumpk n pool
     ω≤bump n = ≤-trans hω (≤-bumpk n pool)

     j2-conv : (X : ℕ) → le (X +ℕ 0) ((9 +ℕ jφ0) +ℕ (0 +ℕ kbudget ι ι kγ))
             → le (X +ℕ 0) (j2 +ℕ (0 +ℕ kbudget ι ι kγ))
     j2-conv X h =
      le-＝-right (ap (_+ℕ (0 +ℕ kbudget ι ι kγ)) (eq-j2 jφ0 ⁻¹)) h

     -- PackDom : additive zone (four summands Dφ0,Dγ,cγ,cφ0 ≤ Y)
     pd : (w : 𝓑) → (Dδ w ⊕ cδ)
                     ≤ ((D2 w ⊕ (acc w ⊕ cφ0))
                         ⊗ bumpk (j2 +ℕ (0 +ℕ kbudget ι ι kγ)) pool)
     pd w =
      transport (λ z → z ≤ (Y ⊗ bumpk (j2 +ℕ (0 +ℕ kbudget ι ι kγ)) pool))
                (reassoc ⁻¹)
                (≤-trans (quad4 (Dφ0 w) (Dγ w) cγ cφ0 Y Dφ≤ Dγ≤ cγ≤ cφ≤)
                         (⊗-mono-right Y (ω≤bump (j2 +ℕ (0 +ℕ kbudget ι ι kγ)))))
      where
       Y : 𝓑
       Y = D2 w ⊕ (acc w ⊕ cφ0)
       reassoc : (Dδ w ⊕ cδ) ＝ (Dφ0 w ⊕ (Dγ w ⊕ (cγ ⊕ cφ0)))
       reassoc = ⊕-assoc (Dφ0 w) (Dγ w) (cγ ⊕ cφ0)
       Dφ≤ : Dφ0 w ≤ Y
       Dφ≤ = ⊕-increasing-right (Dφ0 w) (acc w ⊕ cφ0)
       accpart≤ : acc w ≤ Y
       accpart≤ = ≤-trans (⊕-increasing-right (acc w) cφ0)
                          (⊕-increasing-left (D2 w) (acc w ⊕ cφ0))
       Dγ≤ : Dγ w ≤ Y
       Dγ≤ = ≤-trans (⊕-increasing-right (Dγ w) cγ)
              (≤-trans (⊕-increasing-left Z (Dγ w ⊕ cγ)) accpart≤)
       cγ≤ : cγ ≤ Y
       cγ≤ = ≤-trans (⊕-increasing-left (Dγ w) cγ)
              (≤-trans (⊕-increasing-left Z (Dγ w ⊕ cγ)) accpart≤)
       cφ≤ : cφ0 ≤ Y
       cφ≤ = ≤-trans (⊕-increasing-left (acc w) cφ0)
                     (⊕-increasing-left (D2 w) (acc w ⊕ cφ0))

     -- PackDom : multiplier
     pm : Mδ ≤ bumpk (j2 +ℕ (0 +ℕ kbudget ι ι kγ)) pool
     pm = ≤-trans (mult-absorb Mφ0 Mγ pool 0 hφ hγ hω)
                  (bumpk-le pool (j2-conv 5 (L-pm jφ0 (kbudget ι ι kγ))))

     -- PackDom : budget
     pj : (P : 𝓑)
        → bumpk jδ P ≤ bumpk (j2 +ℕ (0 +ℕ kbudget ι ι kγ)) P
     pj P = bumpk-le P
             (le-＝-right (ap (_+ℕ (0 +ℕ kbudget ι ι kγ)) (eq-j2 jφ0 ⁻¹))
                         (L-pj jφ0 (kbudget ι ι kγ)))

     -- ZApply : rebase packδ-body at constant slack e = 5
     za : ZApply ι ι Fδ acc MH (0 +ℕ kbudget ι ι kγ) D2 cφ0 M2 j2
     za ka =
      ZCont-rebase ι (Fδ ka)
        (λ w → Z ⊕ pr₁ ka w) (λ w → acc w ⊕ pr₁ ka w)
        Dδ D2 Z MH 0 (0 +ℕ kbudget ι ι kγ) cδ cφ0 Mδ M2 jδ ur 5
        I1z (mult-absorb Mφ0 Mγ pool 0 hφ hγ hω) I3z hω
        (packδ-body ka)
      where
       I3z : (P : 𝓑)
           → bumpk (jδ +ℕ 0) P ≤ bumpk (ur +ℕ (0 +ℕ kbudget ι ι kγ)) P
       I3z P = bumpk-le P (L-I3z jφ0 (kbudget ι ι kγ))

       I1z : (w : 𝓑)
           → (Dδ w ⊕ ((Z ⊕ pr₁ ka w) ⊕ cδ))
             ≤ ((D2 w ⊕ ((acc w ⊕ pr₁ ka w) ⊕ cφ0))
                 ⊗ bumpk ((ur +ℕ 5) +ℕ (0 +ℕ kbudget ι ι kγ)) pool)
       I1z w =
        transport (λ z → z ≤ (Y ⊗ bumpk idx pool)) (lhs-eq ⁻¹)
          (≤-trans (pent5 (Dφ0 w) (Dγ w) (pr₁ ka w) cγ cφ0 Y
                          Dφ≤ Dγ≤ ka≤ cγ≤ cφ≤)
                   (⊗-mono-right Y ωω≤))
        where
         idx : ℕ
         idx = (ur +ℕ 5) +ℕ (0 +ℕ kbudget ι ι kγ)
         Y : 𝓑
         Y = D2 w ⊕ ((acc w ⊕ pr₁ ka w) ⊕ cφ0)
         lhs-eq : (Dδ w ⊕ ((Z ⊕ pr₁ ka w) ⊕ cδ))
                  ＝ (Dφ0 w ⊕ (Dγ w ⊕ (pr₁ ka w ⊕ (cγ ⊕ cφ0))))
         lhs-eq = ap (λ z → Dδ w ⊕ (z ⊕ cδ)) (⊕-Z-left (pr₁ ka w))
                  ∙ ⊕-assoc (Dφ0 w) (Dγ w) (pr₁ ka w ⊕ (cγ ⊕ cφ0))
         accpk≤ : (acc w ⊕ pr₁ ka w) ≤ Y
         accpk≤ = ≤-trans (⊕-increasing-right (acc w ⊕ pr₁ ka w) cφ0)
                          (⊕-increasing-left (D2 w) ((acc w ⊕ pr₁ ka w) ⊕ cφ0))
         Dφ≤ : Dφ0 w ≤ Y
         Dφ≤ = ⊕-increasing-right (Dφ0 w) ((acc w ⊕ pr₁ ka w) ⊕ cφ0)
         Dγ≤ : Dγ w ≤ Y
         Dγ≤ = ≤-trans (⊕-increasing-right (Dγ w) cγ)
                (≤-trans (⊕-increasing-left Z (Dγ w ⊕ cγ))
                  (≤-trans (⊕-increasing-right (acc w) (pr₁ ka w)) accpk≤))
         ka≤ : pr₁ ka w ≤ Y
         ka≤ = ≤-trans (⊕-increasing-left (acc w) (pr₁ ka w)) accpk≤
         cγ≤ : cγ ≤ Y
         cγ≤ = ≤-trans (⊕-increasing-left (Dγ w) cγ)
                (≤-trans (⊕-increasing-left Z (Dγ w ⊕ cγ))
                  (≤-trans (⊕-increasing-right (acc w) (pr₁ ka w)) accpk≤))
         cφ≤ : cφ0 ≤ Y
         cφ≤ = ≤-trans (⊕-increasing-left (acc w ⊕ pr₁ ka w) cφ0)
                       (⊕-increasing-left (D2 w) ((acc w ⊕ pr₁ ka w) ⊕ cφ0))
         ωω≤ : (ω ⊗ ω) ≤ bumpk idx pool
         ωω≤ = ≤-trans (⊗-mono-left hω ω)
                (≤-trans (⊗-mono-right pool hω)
                  (≤-trans (⊗-≤-bump pool)
                           (bumpk-le pool (L-I1z jφ0 (kbudget ι ι kγ)))))

\end{code}
