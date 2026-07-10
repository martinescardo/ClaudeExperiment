Design H, stage 2d(viii-c): `packS` — the outer pack of the `S` combinator
over the tower (`ρ = σ = τ = ι`), assembled.

Consuming the first argument `kφ` (function-typed), `packS` produces the
zone pack of `FS kφ = (F2 kφ , pack2 kφ)` (`MultHereditaryH13`). The
`PackDom` obligations dominate `kφ`'s partial-application data (additive
`Dφ ⊕ cφ`, multiplier `Mφ ⊗ ω`, budget `j₂ = rbb ι (3 +ℕ jφ) 5`); the inner
`ZApply` rebases `pack2`'s body by one `ZCont-rebase` **at the arrow type
`ι ⇒ ι`** — the lemma propagates the four leaf invariants through the arrow
structure — at the constant rebase parameters `u = 9 , e = 2`, so the
output budget `jS = rbb (ι ⇒ ι) 9 2` is the literal constant `13`. All
argument budgets ride in the accumulators/pool, keeping `jS` fixed. The
conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryH14
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
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (x-≤-x⊗ ; y-≤-⊗ ; Z<ε₀)
open import Claude.BrouwerOrdinals.MultAffine fe using (ω-pos)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; ω-valid)
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
 using (+ℕ-zero-right ; +ℕ-assoc ; bumpk-+ ; ≤-bumpk ; rbb)
open import Claude.DialogueTreeHeight.MultHereditaryH3 fe
 using (ZCont-rebase)
open import Claude.DialogueTreeHeight.MultHereditaryH4 fe
 using (⊕-Z-left)
open import Claude.DialogueTreeHeight.MultHereditaryH10 fe
 using (le ; bumpk-le ; le-refl ; le-trans ; le-add-right ;
        le-+ℕ-right ; le-＝-left ; le-＝-right)
open import Claude.DialogueTreeHeight.MultHereditaryH8 fe
 using (quad4)
open import Claude.DialogueTreeHeight.MultHereditaryH12 fe
 using (eq-j2)
open import Claude.DialogueTreeHeight.MultHereditaryH13 fe
 using (module Spack2 ; pent5)

\end{code}

The `S` data map and its outer pack.

\begin{code}

FS : 𝕂 (ι ⇒ ι ⇒ ι) → 𝕂 ((ι ⇒ ι) ⇒ (ι ⇒ ι))
FS kφ = Spack2.F2 kφ , Spack2.pack2 kφ

module SpackS where

 DS : 𝓑 → 𝓑
 DS = λ _ → Z
 MS : 𝓑
 MS = ω
 jS : ℕ
 jS = rbb (ι ⇒ ι) 9 2

 packS : ZPack (ι ⇒ ι ⇒ ι) ((ι ⇒ ι) ⇒ (ι ⇒ ι)) FS
 packS = DS , Z , MS , jS
       , ((λ w _ → Z<ε₀) , (λ w w′ _ → ≤-Z))
       , Z<ε₀ , ω-valid , tower-<-ε₀ 0
       , body
  where
   body : (kφ : 𝕂 (ι ⇒ ι ⇒ ι))
        → ZCont ((ι ⇒ ι) ⇒ (ι ⇒ ι)) (FS kφ)
                (λ w → Z ⊕ kadd ι (ι ⇒ ι) kφ w) (Z ⊕ kmult ι (ι ⇒ ι) kφ)
                (0 +ℕ kbudget ι (ι ⇒ ι) kφ) DS Z MS jS
   body kφ = (pd , pm , pj) , za
    where
     Dφ0 : 𝓑 → 𝓑
     Dφ0 = pr₁ (pr₂ kφ)
     cφ0 Mφ0 : 𝓑
     cφ0 = pr₁ (pr₂ (pr₂ kφ))
     Mφ0 = pr₁ (pr₂ (pr₂ (pr₂ kφ)))
     jφ0 : ℕ
     jφ0 = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ kφ))))
     vMφ0 : ValidMult Mφ0
     vMφ0 = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ kφ)))))))

     accS : 𝓑 → 𝓑
     accS = λ w → Z ⊕ (Dφ0 w ⊕ cφ0)
     MHS : 𝓑
     MHS = Z ⊕ Mφ0
     poolS : 𝓑
     poolS = MS ⊕ MHS

     hφ : Mφ0 ≤ poolS
     hφ = ≤-trans (⊕-increasing-left Z Mφ0) (⊕-increasing-left MS MHS)
     hω : ω ≤ poolS
     hω = ⊕-increasing-right MS MHS

     ω≤bump : (n : ℕ) → ω ≤ bumpk n poolS
     ω≤bump n = ≤-trans hω (≤-bumpk n poolS)

     JHS : ℕ
     JHS = 0 +ℕ kbudget ι (ι ⇒ ι) kφ

     -- kbudget ι (ι⇒ι) kφ ≡ jφ0 ; kadd ι (ι⇒ι) kφ ≡ λw→Dφ0 w⊕cφ0 ;
     -- kmult ι (ι⇒ι) kφ ≡ Mφ0 ; kadd (ι⇒ι)(ι⇒ι)(FS kφ) ≡ λw→Dφ0 w⊕cφ0 ;
     -- kmult (ι⇒ι)(ι⇒ι)(FS kφ) ≡ Mφ0 ⊗ ω ; kbudget ≡ rbb ι (3 +ℕ jφ0) 5.

     -- PackDom : zone (two summands Dφ0, cφ0)
     pd : (w : 𝓑) → (Dφ0 w ⊕ cφ0)
                     ≤ ((DS w ⊕ (accS w ⊕ Z)) ⊗ bumpk (jS +ℕ JHS) poolS)
     pd w =
      ≤-trans (≤-trans (⊕-mono-left Dφ0≤ cφ0) (⊕-mono-right YS cφ0≤))
        (≤-trans (⊕-dup-≤-⊗ω YS)
                 (⊗-mono-right YS (ω≤bump (jS +ℕ JHS))))
      where
       YS : 𝓑
       YS = DS w ⊕ (accS w ⊕ Z)
       Dφ0≤ : Dφ0 w ≤ YS
       Dφ0≤ = ≤-trans (⊕-increasing-right (Dφ0 w) cφ0)
               (≤-trans (⊕-increasing-left Z (Dφ0 w ⊕ cφ0))
                 (≤-trans (⊕-increasing-right (accS w) Z)
                          (⊕-increasing-left (DS w) (accS w ⊕ Z))))
       cφ0≤ : cφ0 ≤ YS
       cφ0≤ = ≤-trans (⊕-increasing-left (Dφ0 w) cφ0)
               (≤-trans (⊕-increasing-left Z (Dφ0 w ⊕ cφ0))
                 (≤-trans (⊕-increasing-right (accS w) Z)
                          (⊕-increasing-left (DS w) (accS w ⊕ Z))))

     -- PackDom : multiplier  (Mφ0 ⊗ ω ≤ bump poolS ≤ bumpk (jS+JHS) poolS)
     pm : (Mφ0 ⊗ ω) ≤ bumpk (jS +ℕ JHS) poolS
     pm = ≤-trans (⊗-mono-left hφ ω)
           (≤-trans (⊗-mono-right poolS hω)
             (≤-trans (⊗-≤-bump poolS) (bumpk-le poolS le1)))
      where
       le1 : le 1 (jS +ℕ JHS)
       le1 = (12 +ℕ JHS) , refl

     -- PackDom : budget  (kbudget (FS kφ) = j2 = rbb ι (3+ℕjφ0) 5)
     pj : (P : 𝓑)
        → bumpk (rbb ι (3 +ℕ jφ0) 5) P ≤ bumpk (jS +ℕ JHS) P
     pj P = bumpk-le P
             (le-＝-left (eq-j2 jφ0)
               (le-+ℕ-right JHS ((4 , refl))))

     -- ZApply : rebase pack2's body into packS's context, arrow type ι ⇒ ι
     za : ZApply (ι ⇒ ι) (ι ⇒ ι) (Spack2.F2 kφ)
                 accS MHS JHS DS Z MS jS
     za kγ =
      ZCont-rebase (ι ⇒ ι) (Spack2.F2 kφ kγ)
        (λ w → Z ⊕ kadd ι ι kγ w) (λ w → accS w ⊕ kadd ι ι kγ w)
        Dφ0 DS (Z ⊕ kmult ι ι kγ) (MHS ⊕ kmult ι ι kγ)
        (0 +ℕ kbudget ι ι kγ) (JHS +ℕ kbudget ι ι kγ)
        cφ0 Z (Mφ0 ⊗ ω) MS (rbb ι (3 +ℕ jφ0) 5) 9 2
        I1S I2S I3S I4S (pack2body kγ)
      where
       kb : ℕ
       kb = kbudget ι ι kγ
       pool′ : 𝓑
       pool′ = MS ⊕ (MHS ⊕ kmult ι ι kγ)

       pack2body : (kγ′ : 𝕂 (ι ⇒ ι))
                 → ZCont (ι ⇒ ι) (Spack2.F2 kφ kγ′)
                         (λ w → Z ⊕ kadd ι ι kγ′ w) (Z ⊕ kmult ι ι kγ′)
                         (0 +ℕ kbudget ι ι kγ′)
                         (Spack2.D2 kφ) (Spack2.cφ0 kφ)
                         (Spack2.M2 kφ) (Spack2.j2 kφ)
       pack2body = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂
                     (Spack2.pack2 kφ))))))))

       hφ′ : Mφ0 ≤ pool′
       hφ′ = ≤-trans hφ (⊕-mono-right MS (⊕-increasing-right MHS (kmult ι ι kγ)))
       hγ′ : kmult ι ι kγ ≤ pool′
       hγ′ = ≤-trans (⊕-increasing-left MHS (kmult ι ι kγ))
                     (⊕-increasing-left MS (MHS ⊕ kmult ι ι kγ))
       hω′ : ω ≤ pool′
       hω′ = ⊕-increasing-right MS (MHS ⊕ kmult ι ι kγ)

       I4S : ω ≤ (MS ⊕ (MHS ⊕ kmult ι ι kγ))
       I4S = hω′

       I2S : ((Mφ0 ⊗ ω) ⊕ (Z ⊕ kmult ι ι kγ))
             ≤ bumpk 2 (MS ⊕ (MHS ⊕ kmult ι ι kγ))
       I2S = ≤-trans
              (≤-trans (⊕-mono-left Mφ0ω≤ (Z ⊕ kmult ι ι kγ))
                       (⊕-mono-right (bump pool′) Zkm≤))
              (≤-trans (⊕-dup-≤-⊗ω (bump pool′)) bpω≤)
        where
         Mφ0ω≤ : (Mφ0 ⊗ ω) ≤ bump pool′
         Mφ0ω≤ = ≤-trans (⊗-mono-left hφ′ ω)
                  (≤-trans (⊗-mono-right pool′ hω′) (⊗-≤-bump pool′))
         Zkm≤ : (Z ⊕ kmult ι ι kγ) ≤ bump pool′
         Zkm≤ = transport (λ z → z ≤ bump pool′)
                          ((⊕-Z-left (kmult ι ι kγ)) ⁻¹)
                          (≤-trans hγ′ (≤-bump pool′))
         bpω≤ : ((bump pool′) ⊗ ω) ≤ bumpk 2 pool′
         bpω≤ = ≤-trans (⊗-mono-right (bump pool′)
                          (≤-trans hω′ (≤-bump pool′)))
                        (⊗-≤-bump (bump pool′))

       I3S : (P : 𝓑)
           → bumpk (rbb ι (3 +ℕ jφ0) 5 +ℕ (0 +ℕ kb)) P
             ≤ bumpk (9 +ℕ (JHS +ℕ kb)) P
       I3S P =
        bumpk-le P
          (le-＝-left (ap (_+ℕ (0 +ℕ kb)) (eq-j2 jφ0))
            (le-＝-right (+ℕ-assoc 9 jφ0 kb)
              (le-refl ((9 +ℕ jφ0) +ℕ kb))))

       I1S : (w : 𝓑)
           → (Dφ0 w ⊕ ((Z ⊕ kadd ι ι kγ w) ⊕ cφ0))
             ≤ ((DS w ⊕ ((accS w ⊕ kadd ι ι kγ w) ⊕ Z))
                 ⊗ bumpk ((9 +ℕ 2) +ℕ (JHS +ℕ kb)) pool′)
       I1S w =
        transport (λ z → z ≤ (YS ⊗ bumpk idx pool′)) (lhs-eq ⁻¹)
          (≤-trans (quad4 (Dφ0 w) (Dγ w) cγ cφ0 YS
                          Dφ0≤ Dγ≤ cγ≤ cφ0≤)
                   (⊗-mono-right YS (≤-trans hω′ (≤-bumpk idx pool′))))
        where
         Dγ : 𝓑 → 𝓑
         Dγ = pr₁ (pr₂ kγ)
         cγ : 𝓑
         cγ = pr₁ (pr₂ (pr₂ kγ))
         idx : ℕ
         idx = (9 +ℕ 2) +ℕ (JHS +ℕ kb)
         P1 P2 P3 : 𝓑
         P1 = Z ⊕ (Dφ0 w ⊕ cφ0)
         P2 = P1 ⊕ (Dγ w ⊕ cγ)
         P3 = P2 ⊕ Z
         YS : 𝓑
         YS = Z ⊕ P3
         lhs-eq : (Dφ0 w ⊕ ((Z ⊕ (Dγ w ⊕ cγ)) ⊕ cφ0))
                  ＝ (Dφ0 w ⊕ (Dγ w ⊕ (cγ ⊕ cφ0)))
         lhs-eq = ap (λ z → Dφ0 w ⊕ (z ⊕ cφ0)) (⊕-Z-left (Dγ w ⊕ cγ))
                  ∙ ap (Dφ0 w ⊕_) (⊕-assoc (Dγ w) cγ cφ0)
         P3≤YS : P3 ≤ YS
         P3≤YS = ⊕-increasing-left Z P3
         P2≤YS : P2 ≤ YS
         P2≤YS = ≤-trans (⊕-increasing-right P2 Z) P3≤YS
         Dφ0≤ : Dφ0 w ≤ YS
         Dφ0≤ = ≤-trans (⊕-increasing-right (Dφ0 w) cφ0)
                 (≤-trans (⊕-increasing-left Z (Dφ0 w ⊕ cφ0))
                   (≤-trans (⊕-increasing-right P1 (Dγ w ⊕ cγ)) P2≤YS))
         cφ0≤ : cφ0 ≤ YS
         cφ0≤ = ≤-trans (⊕-increasing-left (Dφ0 w) cφ0)
                 (≤-trans (⊕-increasing-left Z (Dφ0 w ⊕ cφ0))
                   (≤-trans (⊕-increasing-right P1 (Dγ w ⊕ cγ)) P2≤YS))
         Dγ≤ : Dγ w ≤ YS
         Dγ≤ = ≤-trans (⊕-increasing-right (Dγ w) cγ)
                (≤-trans (⊕-increasing-left P1 (Dγ w ⊕ cγ)) P2≤YS)
         cγ≤ : cγ ≤ YS
         cγ≤ = ≤-trans (⊕-increasing-left (Dγ w) cγ)
                (≤-trans (⊕-increasing-left P1 (Dγ w ⊕ cγ)) P2≤YS)

\end{code}
