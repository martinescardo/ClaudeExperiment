Design H, stage 2d(iv): the `S`-diagonal pack at a ground shared argument
and ground middle — the core of `GoodH-S`, verified.

`GoodH-S`'s data map is the diagonal `Fδ ka = pr₁ (pr₁ kφ ka) (pr₁ kγ ka)`
— apply `φ`'s map to the shared argument, then that result's map to `γ`'s.
The pack of this diagonal (`packδ`) is the crux of the `S` combinator over
the tower, and this module builds and verifies it for a *ground* shared
argument (`ρ = ι`) and *ground middle* (`σ = ι`), any result type `τ`.

The construction, and the budget resolution it validates: consuming the
shared argument `ka` in `φ`'s pack yields (its second slot) a `ZApply` that,
fed the γ-value `Fγ ka`, produces the "raw" diagonal `ZCont` — with the
γ-value sitting in the accumulator. `γ`'s own pack (consumed at `ka`) bounds
that value, and one `ZCont-rebase` folds it into the diagonal's zone and
multiplier. **The key fact — which dissolves the budget tension flagged in
the earlier paper derivation — is that `packδ` is built with both `kφ` and
`kγ` in scope, so `γ`'s budget `jγ` is carried in the *multiplier*
(`Bγ = bumpk jγ Mγ`, placed inside `Mδ`), and the diagonal's *budget*
`jδ = rbb τ jφ 0` depends only on `jφ`.** So the rebase runs at `u = jφ`,
`e = 0`; `γ`'s contribution is entirely multiplicative.

The fn-middle case (`σ` an arrow, where the γ-value is fed to `φ`'s slot as
a *function* and its `PackDom` supplies the rebase hypotheses) and the outer
packs (`pack2`, `packS`) build on this same rebase pattern; they are the
remaining constructions for the full `GoodH-S`. The conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryH8
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
 using (𝕋 ; GoodT ; GoodT-⊕)
open import Claude.DialogueTreeHeight.MultHereditaryG fe
 using (GFun)
open import Claude.DialogueTreeHeight.MultHereditaryFAff fe
 using (⊕-trip-≤-⊗ω)
open import Claude.DialogueTreeHeight.MultHereditaryFAff2 fe
 using (⊕-quad-≤-⊗ω)
open import Claude.BrouwerOrdinals.MultBump fe
 using (bump ; bumpk ; bumpk-mono ; ≤-bump ; ⊗-≤-bump ;
        bumpk-valid ; bumpk-<-ε₀)
open import Claude.DialogueTreeHeight.MultHereditaryH fe
 using (_+ℕ_ ; 𝕂 ; ZPack ; ZApply ; ZCont ; PackDom ;
        kadd ; kmult ; kbudget)
open import Claude.DialogueTreeHeight.MultHereditaryH2 fe
 using (+ℕ-zero-right ; bumpk-+ ; ≤-bumpk ; bumpk-pad ; rbb)
open import Claude.DialogueTreeHeight.MultHereditaryH3 fe
 using (ZCont-rebase)
open import Claude.DialogueTreeHeight.MultHereditaryH10 fe
 using (le ; bumpk-le ; le-trans ; le-add-right ; le-add-left ;
        le-+ℕ-right ; le-＝-left ; le-＝-right)
open import Claude.DialogueTreeHeight.MultHereditaryH11 fe
 using (diag-absorb)

\end{code}

Heterogeneous triple and quadruple absorption.

\begin{code}

trip3r : (a b c z : 𝓑) → a ≤ z → b ≤ z → c ≤ z → (a ⊕ (b ⊕ c)) ≤ (z ⊗ ω)
trip3r a b c z ha hb hc =
 ≤-trans (⊕-mono-left ha (b ⊕ c))
         (≤-trans (⊕-mono-right z (⊕-mono-left hb c))
                  (≤-trans (⊕-mono-right z (⊕-mono-right z hc))
                           (⊕-trip-≤-⊗ω z)))

quad4 : (a b c d z : 𝓑) → a ≤ z → b ≤ z → c ≤ z → d ≤ z
      → (a ⊕ (b ⊕ (c ⊕ d))) ≤ (z ⊗ ω)
quad4 a b c d z ha hb hc hd =
 ≤-trans (⊕-mono-left ha (b ⊕ (c ⊕ d)))
   (≤-trans (⊕-mono-right z (⊕-mono-left hb (c ⊕ d)))
     (≤-trans (⊕-mono-right z (⊕-mono-right z (⊕-mono-left hc d)))
       (≤-trans (⊕-mono-right z (⊕-mono-right z (⊕-mono-right z hd)))
                (⊕-quad-≤-⊗ω z))))

\end{code}

The diagonal pack at ground shared argument and ground middle, parameterized
by the two argument data.

\begin{code}

module Sδ-ground
 (τ : type)
 (kφ : 𝕂 (ι ⇒ ι ⇒ τ))
 (kγ : 𝕂 (ι ⇒ ι))
 where

 Fφ : GFun → 𝕂 (ι ⇒ τ)
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
 zaφ : ZApply ι (ι ⇒ τ) Fφ (λ _ → Z) Z 0 Dφ cφ Mφ jφ
 zaφ = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ kφ))))))))

 Fγ : GFun → GFun
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
 zaγ : ZApply ι ι Fγ (λ _ → Z) Z 0 Dγ cγ Mγ jγ
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
 Mδ = bumpk 3 base₀
 vMδ : ValidMult Mδ
 vMδ = bumpk-valid 3 vbase₀
 Mδε : Mδ < ε₀
 Mδε = bumpk-<-ε₀ 3 base₀ε

 Dδ : 𝓑 → 𝓑
 Dδ = λ w → Dφ w ⊕ Dγ w
 gDδ : GoodT ι Dδ
 gDδ = GoodT-⊕ Dφ Dγ gDφ gDγ
 cδ : 𝓑
 cδ = cγ ⊕ cφ
 cδε : cδ < ε₀
 cδε = ⊕-<-ε₀ cγ cφ cγε cφε

 uδ : ℕ
 uδ = (2 +ℕ jγ) +ℕ jφ
 jδ : ℕ
 jδ = rbb τ uδ 0

 Fδ : GFun → 𝕂 τ
 Fδ ka = pr₁ (Fφ ka) (Fγ ka)

 vMγω : S Z ≤ (Mγ ⊗ ω)
 vMγω = ≤-trans ω-pos (y-≤-⊗ Mγ ω (pr₁ vMγ))
 Mφ≤base₀ : Mφ ≤ base₀
 Mφ≤base₀ = x-≤-x⊗ Mφ (Mγ ⊗ ω) vMγω
 ω≤base₀ : ω ≤ base₀
 ω≤base₀ = ≤-trans (y-≤-⊗ Mγ ω (pr₁ vMγ)) (y-≤-⊗ Mφ (Mγ ⊗ ω) (pr₁ vMφ))
 Mφ≤Mδ : Mφ ≤ Mδ
 Mφ≤Mδ = ≤-trans Mφ≤base₀ (≤-bumpk 3 base₀)
 ω≤Mδ : ω ≤ Mδ
 ω≤Mδ = ≤-trans ω≤base₀ (≤-bumpk 3 base₀)

 leKM : le (2 +ℕ (jγ +ℕ 0)) (((uδ +ℕ 0) +ℕ 0) +ℕ 3)
 leKM = le-＝-left (ap (2 +ℕ_) (+ℕ-zero-right jγ))
          (le-＝-right e2 core)
  where
   e2 : (uδ +ℕ 3) ＝ (((uδ +ℕ 0) +ℕ 0) +ℕ 3)
   e2 = ap (_+ℕ 3)
          ((+ℕ-zero-right uδ) ⁻¹ ∙ (+ℕ-zero-right (uδ +ℕ 0)) ⁻¹)
   core : le (2 +ℕ jγ) (uδ +ℕ 3)
   core = le-trans (le-add-right (2 +ℕ jγ) jφ)
                   (le-add-right uδ 3)

 keyM : ((ω ⊗ Bγ) ⊗ ω) ≤ bumpk ((uδ +ℕ 0) +ℕ 0) (Mδ ⊕ Z)
 keyM = ≤-trans (diag-absorb Mφ Mγ (jγ +ℕ 0) (pr₁ vMφ) (pr₁ vMγ))
          (transport (λ z → bumpk (2 +ℕ (jγ +ℕ 0)) base₀ ≤ z)
                     (bumpk-+ ((uδ +ℕ 0) +ℕ 0) 3 base₀)
                     (bumpk-le base₀ leKM))

\end{code}

The diagonal `ZCont`, per shared argument.

\begin{code}

 packδ-body : (ka : GFun)
            → ZCont τ (Fδ ka) (λ w → Z ⊕ pr₁ ka w) Z 0 Dδ cδ Mδ jδ
 packδ-body ka =
  ZCont-rebase τ (Fδ ka)
    Asrc accₐ Dφ Dδ Z Z 0 0 cφ cδ Mφ Mδ jφ uδ 0
    I1 Mφ≤Mδ I3 ω≤Mδ (zaφ2 (Fγ ka))
  where
   accₐ : 𝓑 → 𝓑
   accₐ = λ w → Z ⊕ pr₁ ka w
   Asrc : 𝓑 → 𝓑
   Asrc = λ w → accₐ w ⊕ pr₁ (Fγ ka) w
   zaφ2 : (b : GFun)
        → ZCont τ (pr₁ (Fφ ka) b) (λ w → accₐ w ⊕ pr₁ b w) Z 0 Dφ cφ Mφ jφ
   zaφ2 = pr₂ (zaφ ka)

   I3 : (P : 𝓑) → bumpk (jφ +ℕ 0) P ≤ bumpk (uδ +ℕ 0) P
   I3 P = bumpk-le P (le-+ℕ-right 0 (le-add-left (2 +ℕ jγ) jφ))

   I1 : (w : 𝓑) → (Dφ w ⊕ (Asrc w ⊕ cφ))
        ≤ ((Dδ w ⊕ (accₐ w ⊕ cδ)) ⊗ bumpk ((uδ +ℕ 0) +ℕ 0) (Mδ ⊕ Z))
   I1 w = transport
           (λ z → z ≤ ((Dδ w ⊕ (accₐ w ⊕ cδ))
                        ⊗ bumpk ((uδ +ℕ 0) +ℕ 0) (Mδ ⊕ Z)))
           (reassoc ⁻¹)
           (≤-trans quad finish)
    where
     X : 𝓑
     X = pr₁ (Fγ ka) w
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
     X≤Q = ≤-trans (zaγ ka w)
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

     finish : (Q ⊗ ω) ≤ (Y ⊗ bumpk ((uδ +ℕ 0) +ℕ 0) (Mδ ⊕ Z))
     finish = transport (λ z → z ≤ (Y ⊗ bumpk ((uδ +ℕ 0) +ℕ 0) (Mδ ⊕ Z)))
                        ((⊗-assoc Y (ω ⊗ Bγ) ω) ⁻¹)
                        (⊗-mono-right Y keyM)

 packδ : ZPack ι τ Fδ
 packδ = Dδ , cδ , Mδ , jδ , gDδ , cδε , vMδ , Mδε , packδ-body

\end{code}
