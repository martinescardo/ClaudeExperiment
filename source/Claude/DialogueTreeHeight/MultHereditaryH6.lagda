Design H, stage 2d(ii): the recursor over the Howard tower — `GoodH-Iter`.

The recursor's tower datum: given an argument pack `kg : 𝕂 (ι ⇒ ι)`, the
data maps are `MultHereditaryG`'s orbit engine applied through the pack
(`FI3 kg ka kν = dsum (dOrbit (pr₁ kg) (pack-to-Tracked …) ka) kν`), so the
bound relation is *definitionally* module 45's `BndD-Iter`/`BndD-orbit`.
The new content is the three zone packs: the inner constant-plus-count pack
(`pack3`, one chain), the start-consuming pack (`pack2`, multiplier
`bumpk 3 M̂` where `M̂` is the tracked multiplier of `kg` — the orbit raise
`bump M̂` and the absorptions fit with a bump to spare), and the outer pack
(`packI`, budget `3`, whose multiplier obligation reduces to the *identity
of budgets* `bumpk 3 M̂ ＝ bumpk (3 + jg) Mg` by `bumpk-+` — the recursor
costs exactly the argument's budget plus three). The `GoodT` side is
`MultHereditaryH5`'s good-inputs orbit; the weight-level bound is Design
F's `orbit-pt` induction, verbatim. The conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryH6
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe
 using (ω ; _⊗_ ; ⊕-mono-left ; ⊕-assoc)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right ;
        ⊕-increasing-right ; ⊕-<-ε₀ ; tower-<-ε₀)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊗-assoc ; ⊕-increasing-left)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (x-≤-x⊗)
open import Claude.BrouwerOrdinals.MultAffine fe using (ω-pos)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; ω-valid)
open import Claude.DialogueTreeHeight.Majorant fe
 using (Maj ; μ-Iter)
open import Claude.DialogueTreeHeight.MultHereditaryF fe
 using (𝕋 ; GoodT ; Torbit ; GoodT-iter ; GoodT-⊕)
open import Claude.DialogueTreeHeight.MultHereditaryFAff fe
 using (⊕-dup-≤-⊗ω ; ⊕-trip-≤-⊗ω)
open import Claude.DialogueTreeHeight.MultHereditaryG fe
 using (GFun ; Tracked ; dOrbit ; dsum ; BndD-orbit ; BndD-Iter)
open import Claude.BrouwerOrdinals.MultBump fe
 using (bump ; bumpk ; bumpk-mono ; ≤-bump ; ⊗-≤-bump ;
        bumpk-valid ; bumpk-<-ε₀)
open import Claude.DialogueTreeHeight.MultHereditaryH fe
 using (_+ℕ_ ; 𝕂 ; ZPack ; ZApply ; ZCont ; PackDom ;
        kadd ; kmult ; kbudget)
open import Claude.DialogueTreeHeight.MultHereditaryH2 fe
 using (≤-bumpk ; bumpk-+ ; +ℕ-zero-right ; ω-≤-bump)
open import Claude.DialogueTreeHeight.MultHereditaryH4 fe
 using (BndH ; LT ; BndL ; GoodH ; pack-to-Tracked)
open import Claude.DialogueTreeHeight.MultHereditaryH5 fe
 using (orbit-goodT ; BndH-to-aff-good)

\end{code}

Three summands each below a zone are absorbed by `⊗ ω`.

\begin{code}

trip3 : (a b c z : 𝓑) → a ≤ z → b ≤ z → c ≤ z → ((a ⊕ b) ⊕ c) ≤ (z ⊗ ω)
trip3 a b c z ha hb hc =
 ≤-trans
  (≤-trans (⊕-mono-left (≤-trans (⊕-mono-left ha b) (⊕-mono-right z hb)) c)
           (⊕-mono-right (z ⊕ z) hc))
  (transport (λ q → q ≤ (z ⊗ ω)) ((⊕-assoc z z z) ⁻¹) (⊕-trip-≤-⊗ω z))

\end{code}

The pack constructions, parameterized by the recursor's argument datum.

\begin{code}

module IterPack (kg : 𝕂 (ι ⇒ ι)) where

 Fg : GFun → GFun
 Fg = pr₁ kg

 Dg : 𝓑 → 𝓑
 Dg = pr₁ (pr₂ kg)

 cg Mg : 𝓑
 cg = pr₁ (pr₂ (pr₂ kg))
 Mg = pr₁ (pr₂ (pr₂ (pr₂ kg)))

 jg : ℕ
 jg = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ kg))))

 gDg : GoodT ι Dg
 gDg = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ kg)))))

 cgε : cg < ε₀
 cgε = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ kg))))))

 vMg : ValidMult Mg
 vMg = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ kg)))))))

 Mgε : Mg < ε₀
 Mgε = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ kg))))))))

 trkg : Tracked Fg
 trkg = pack-to-Tracked Fg (pr₂ kg)

 M̂ : 𝓑
 M̂ = bumpk (jg +ℕ 0) (Mg ⊕ Z)

 P : 𝓑
 P = bump M̂

 M̂+ : S Z ≤ M̂
 M̂+ = ≤-trans (pr₁ vMg) (≤-bumpk (jg +ℕ 0) (Mg ⊕ Z))

 P+ : S Z ≤ P
 P+ = ≤-trans M̂+ (≤-bump M̂)

 vM̂ : ValidMult M̂
 vM̂ = bumpk-valid (jg +ℕ 0) vMg

 M̂ε : M̂ < ε₀
 M̂ε = bumpk-<-ε₀ (jg +ℕ 0) Mgε

 M₂ : 𝓑
 M₂ = bumpk 3 M̂

 lemA : (ω ⊗ P) ≤ bumpk 2 M̂
 lemA = ≤-trans (⊗-mono-left (ω-≤-bump M̂ M̂+) P) (⊗-≤-bump P)

 lemA3 : (ω ⊗ P) ≤ M₂
 lemA3 = ≤-trans lemA (≤-bump (bumpk 2 M̂))

 lemB : ((ω ⊗ P) ⊗ ω) ≤ M₂
 lemB = ≤-trans (⊗-mono-left lemA ω)
         (≤-trans (⊗-mono-right (bumpk 2 M̂)
                    (≤-trans (ω-≤-bump M̂ M̂+) (≤-bump (bump M̂))))
                  (⊗-≤-bump (bumpk 2 M̂)))

 ob : GFun → GFun
 ob ka = dOrbit Fg trkg ka

 FI3 : GFun → GFun → GFun
 FI3 ka kν = dsum (ob ka) kν

\end{code}

The inner pack: constant orbit datum plus the count.

\begin{code}

 pack3 : (ka : GFun) → ZPack ι ι (FI3 ka)
 pack3 ka =
  pr₁ (ob ka) , Z , ω , 0
  , pr₂ (ob ka) , Z<ε₀' , ω-valid , tower-<-ε₀ 0
  , (λ kν w →
      ≤-trans (⊕-mono-right (pr₁ (ob ka) w) (⊕-increasing-left Z (pr₁ kν w)))
              (x-≤-x⊗ (pr₁ (ob ka) w ⊕ (Z ⊕ pr₁ kν w)) ω ω-pos))
  where
   Z<ε₀' : Z < ε₀
   Z<ε₀' = ≤-trans (≤-S ≤-Z) (tower-<-ε₀ 0)

\end{code}

The middle pack: consuming the start. The orbit datum's three zone summands
sit below the accumulated zone, and the multipliers absorb into `bumpk 3`.

\begin{code}

 FI2 : GFun → 𝕂 (ι ⇒ ι)
 FI2 ka = FI3 ka , pack3 ka

 pack2 : ZPack ι (ι ⇒ ι) FI2
 pack2 =
  D₂ , Z , M₂ , 0
  , ((λ w p → ⊕-<-ε₀ (Dg w) cg (pr₁ gDg w p) cgε)
    , (λ w w′ q → ⊕-mono-left (pr₂ gDg w w′ q) cg))
  , Z<ε₀' , bumpk-valid 3 vM̂ , bumpk-<-ε₀ 3 M̂ε
  , body
  where
   Z<ε₀' : Z < ε₀
   Z<ε₀' = ≤-trans (≤-S ≤-Z) (tower-<-ε₀ 0)

   D₂ : 𝓑 → 𝓑
   D₂ = λ w → Dg w ⊕ cg

   body : (ka : GFun)
        → ZCont (ι ⇒ ι) (FI2 ka) (λ w → Z ⊕ pr₁ ka w) Z 0 D₂ Z M₂ 0
   body ka = (pd , pm , pj) , ground
    where
     zone : 𝓑 → 𝓑
     zone = λ w → D₂ w ⊕ (Z ⊕ pr₁ ka w)

     obz : (w : 𝓑) → pr₁ (ob ka) w ≤ ((zone w ⊗ ω) ⊗ P)
     obz w = ⊗-mono-left
              (trip3 (Dg w) (pr₁ ka w) cg (zone w)
                (≤-trans (⊕-increasing-right (Dg w) cg)
                         (⊕-increasing-right (D₂ w) (Z ⊕ pr₁ ka w)))
                (≤-trans (⊕-increasing-left Z (pr₁ ka w))
                         (⊕-increasing-left (D₂ w) (Z ⊕ pr₁ ka w)))
                (≤-trans (⊕-increasing-left (Dg w) cg)
                         (⊕-increasing-right (D₂ w) (Z ⊕ pr₁ ka w))))
              P

     pd : (w : 𝓑) → (pr₁ (ob ka) w ⊕ Z) ≤ ((D₂ w ⊕ ((Z ⊕ pr₁ ka w) ⊕ Z)) ⊗ M₂)
     pd w = ≤-trans (obz w)
             (transport (λ q → q ≤ (zone w ⊗ M₂)) ((⊗-assoc (zone w) ω P) ⁻¹)
                        (⊗-mono-right (zone w) lemA3))

     pm : ω ≤ M₂
     pm = ≤-trans (ω-≤-bump M̂ M̂+)
                  (≤-trans (≤-bump (bumpk 1 M̂)) (≤-bump (bumpk 2 M̂)))

     pj : (Q : 𝓑) → bumpk 0 Q ≤ Q
     pj Q = ≤-refl Q

     ground : (kν : GFun) (w : 𝓑)
            → pr₁ (FI3 ka kν) w
              ≤ ((D₂ w ⊕ (((Z ⊕ pr₁ ka w) ⊕ pr₁ kν w) ⊕ Z)) ⊗ M₂)
     ground kν w =
      ≤-trans
       (≤-trans
         (⊕-mono-left (≤-trans (obz′ w) (x-lift w)) (pr₁ kν w))
         (≤-trans (⊕-mono-right X (ν≤X w)) (⊕-dup-≤-⊗ω X)))
       (transport (λ q → q ≤ (zone₄ w ⊗ M₂))
                  ((⊗-assoc (zone₄ w) (ω ⊗ P) ω) ⁻¹)
                  (⊗-mono-right (zone₄ w) lemB))
      where
       zone₄ : 𝓑 → 𝓑
       zone₄ = λ w′ → D₂ w′ ⊕ ((Z ⊕ pr₁ ka w′) ⊕ pr₁ kν w′)

       X : 𝓑
       X = zone₄ w ⊗ (ω ⊗ P)

       obz′ : (w′ : 𝓑) → pr₁ (ob ka) w′ ≤ ((zone₄ w′ ⊗ ω) ⊗ P)
       obz′ w′ = ⊗-mono-left
                  (trip3 (Dg w′) (pr₁ ka w′) cg (zone₄ w′)
                    (≤-trans (⊕-increasing-right (Dg w′) cg)
                             (⊕-increasing-right (D₂ w′) tail))
                    (≤-trans (⊕-increasing-left Z (pr₁ ka w′))
                      (≤-trans (⊕-increasing-right (Z ⊕ pr₁ ka w′)
                                                   (pr₁ kν w′))
                               (⊕-increasing-left (D₂ w′) tail)))
                    (≤-trans (⊕-increasing-left (Dg w′) cg)
                             (⊕-increasing-right (D₂ w′) tail)))
                  P
        where
         tail : 𝓑
         tail = (Z ⊕ pr₁ ka w′) ⊕ pr₁ kν w′

       x-lift : (w′ : 𝓑) → ((zone₄ w′ ⊗ ω) ⊗ P) ≤ (zone₄ w′ ⊗ (ω ⊗ P))
       x-lift w′ = transport (λ q → ((zone₄ w′ ⊗ ω) ⊗ P) ≤ q)
                             (⊗-assoc (zone₄ w′) ω P)
                             (≤-refl ((zone₄ w′ ⊗ ω) ⊗ P))

       ν≤X : (w′ : 𝓑) → pr₁ kν w′ ≤ (zone₄ w′ ⊗ (ω ⊗ P))
       ν≤X w′ = ≤-trans
                 (≤-trans (⊕-increasing-left (Z ⊕ pr₁ ka w′) (pr₁ kν w′))
                          (⊕-increasing-left (D₂ w′) _))
                 (x-≤-x⊗ (zone₄ w′) (ω ⊗ P)
                   (≤-trans ω-pos (x-≤-x⊗ ω P P+)))

\end{code}

The outer pack: consuming the tower argument itself. The argument's zone
data is exactly the accumulator entry, and the multiplier obligation is the
budget identity `bumpk 3 M̂ ＝ bumpk (3 + jg) Mg`.

\begin{code}

 BI : 𝓑
 BI = bumpk (3 +ℕ jg) (ω ⊕ (Z ⊕ Mg))

 M₂BI : M₂ ≤ BI
 M₂BI = transport (λ q → q ≤ BI) (eqM ⁻¹)
         (bumpk-mono (3 +ℕ jg)
           (≤-trans (⊕-increasing-left Z Mg)
                    (⊕-increasing-left ω (Z ⊕ Mg))))
  where
   eqM : M₂ ＝ bumpk (3 +ℕ jg) (Mg ⊕ Z)
   eqM = (bumpk-+ 3 (jg +ℕ 0) (Mg ⊕ Z)) ⁻¹
         ∙ ap (λ n → bumpk (3 +ℕ n) (Mg ⊕ Z)) (+ℕ-zero-right jg)

 ωBI : ω ≤ BI
 ωBI = ≤-trans (⊕-increasing-right ω (Z ⊕ Mg)) (≤-bumpk (3 +ℕ jg) _)

 BI+ : S Z ≤ BI
 BI+ = ≤-trans ω-pos ωBI

\end{code}

\begin{code}

FI : (kg : 𝕂 (ι ⇒ ι)) → 𝕂 (ι ⇒ ι ⇒ ι)
FI kg = IterPack.FI2 kg , IterPack.pack2 kg

packI : ZPack (ι ⇒ ι) (ι ⇒ ι ⇒ ι) FI
packI =
 (λ _ → Z) , Z , ω , 3
 , ((λ w _ → Z<ε₀') , (λ w w′ _ → ≤-Z))
 , Z<ε₀' , ω-valid , tower-<-ε₀ 0
 , body
 where
  Z<ε₀' : Z < ε₀
  Z<ε₀' = ≤-trans (≤-S ≤-Z) (tower-<-ε₀ 0)

  body : (kg : 𝕂 (ι ⇒ ι))
       → ZCont (ι ⇒ ι ⇒ ι) (FI kg)
              (λ w → Z ⊕ kadd ι ι kg w)
              (Z ⊕ kmult ι ι kg) (0 +ℕ kbudget ι ι kg)
              (λ _ → Z) Z ω 3
  body kg = (pd₂ , pm₂ , pj₂) , inner
   where
    open IterPack kg

    A₁ : 𝓑 → 𝓑
    A₁ = λ w → Z ⊕ (Dg w ⊕ cg)

    zoneOf : (𝓑 → 𝓑) → 𝓑 → 𝓑
    zoneOf A = λ w → Z ⊕ (A w ⊕ Z)

    z-in : (A : 𝓑 → 𝓑) (w : 𝓑) → A w ≤ zoneOf A w
    z-in A w = ≤-trans (⊕-increasing-right (A w) Z)
                       (⊕-increasing-left Z (A w ⊕ Z))

    pd₂ : (w : 𝓑) → ((Dg w ⊕ cg) ⊕ Z) ≤ (((λ _ → Z) w ⊕ (A₁ w ⊕ Z)) ⊗ BI)
    pd₂ w = ≤-trans (⊕-increasing-left Z (Dg w ⊕ cg))
             (≤-trans (z-in A₁ w)
                      (x-≤-x⊗ (zoneOf A₁ w) BI BI+))

    pm₂ : M₂ ≤ BI
    pm₂ = M₂BI

    pj₂ : (Q : 𝓑) → bumpk 0 Q ≤ bumpk (3 +ℕ jg) Q
    pj₂ Q = ≤-bumpk (3 +ℕ jg) Q

    inner : (ka : GFun)
          → ZCont (ι ⇒ ι) (FI2 ka) (λ w → A₁ w ⊕ pr₁ ka w)
                 (Z ⊕ Mg) jg (λ _ → Z) Z ω 3
    inner ka = (pd₃ , pm₃ , pj₃) , ground
     where
      A₂ : 𝓑 → 𝓑
      A₂ = λ w → A₁ w ⊕ pr₁ ka w

      sum-Dg : (A : 𝓑 → 𝓑) → ((w : 𝓑) → A₁ w ≤ A w)
             → (w : 𝓑) → Dg w ≤ zoneOf A w
      sum-Dg A hA w =
       ≤-trans (⊕-increasing-right (Dg w) cg)
        (≤-trans (⊕-increasing-left Z (Dg w ⊕ cg))
          (≤-trans (hA w) (z-in A w)))

      sum-cg : (A : 𝓑 → 𝓑) → ((w : 𝓑) → A₁ w ≤ A w)
             → (w : 𝓑) → cg ≤ zoneOf A w
      sum-cg A hA w =
       ≤-trans (⊕-increasing-left (Dg w) cg)
        (≤-trans (⊕-increasing-left Z (Dg w ⊕ cg))
          (≤-trans (hA w) (z-in A w)))

      obzB : (A : 𝓑 → 𝓑) → ((w : 𝓑) → A₁ w ≤ A w)
           → ((w : 𝓑) → pr₁ ka w ≤ zoneOf A w)
           → (w : 𝓑) → pr₁ (ob ka) w ≤ ((zoneOf A w ⊗ ω) ⊗ P)
      obzB A hA hka w =
       ⊗-mono-left
        (trip3 (Dg w) (pr₁ ka w) cg (zoneOf A w)
          (sum-Dg A hA w) (hka w) (sum-cg A hA w))
        P

      pd₃ : (w : 𝓑) → (pr₁ (ob ka) w ⊕ Z)
                       ≤ (((λ _ → Z) w ⊕ (A₂ w ⊕ Z)) ⊗ BI)
      pd₃ w = ≤-trans
               (obzB A₂ (λ w′ → ⊕-increasing-right (A₁ w′) (pr₁ ka w′))
                 (λ w′ → ≤-trans (⊕-increasing-left (A₁ w′) (pr₁ ka w′))
                                 (z-in A₂ w′)) w)
               (transport (λ q → q ≤ (zoneOf A₂ w ⊗ BI))
                          ((⊗-assoc (zoneOf A₂ w) ω P) ⁻¹)
                          (⊗-mono-right (zoneOf A₂ w)
                            (≤-trans lemA3 M₂BI)))

      pm₃ : ω ≤ BI
      pm₃ = ωBI

      pj₃ : (Q : 𝓑) → bumpk 0 Q ≤ bumpk (3 +ℕ jg) Q
      pj₃ Q = ≤-bumpk (3 +ℕ jg) Q

      ground : (kν : GFun) (w : 𝓑)
             → pr₁ (FI3 ka kν) w
               ≤ (((λ _ → Z) w ⊕ ((A₂ w ⊕ pr₁ kν w) ⊕ Z)) ⊗ BI)
      ground kν w =
       ≤-trans
        (≤-trans
          (⊕-mono-left
            (≤-trans (obzB A₃
                       (λ w′ → ≤-trans
                                (⊕-increasing-right (A₁ w′) (pr₁ ka w′))
                                (⊕-increasing-right (A₂ w′) (pr₁ kν w′)))
                       (λ w′ → ≤-trans
                                (⊕-increasing-left (A₁ w′) (pr₁ ka w′))
                                (≤-trans (⊕-increasing-right (A₂ w′)
                                                             (pr₁ kν w′))
                                         (z-in A₃ w′))) w)
                     (x-lift w))
            (pr₁ kν w))
          (≤-trans (⊕-mono-right X (ν≤X w)) (⊕-dup-≤-⊗ω X)))
        (transport (λ q → q ≤ (zoneOf A₃ w ⊗ BI))
                   ((⊗-assoc (zoneOf A₃ w) (ω ⊗ P) ω) ⁻¹)
                   (⊗-mono-right (zoneOf A₃ w) (≤-trans lemB M₂BI)))
       where
        A₃ : 𝓑 → 𝓑
        A₃ = λ w′ → A₂ w′ ⊕ pr₁ kν w′

        X : 𝓑
        X = zoneOf A₃ w ⊗ (ω ⊗ P)

        x-lift : (w′ : 𝓑) → ((zoneOf A₃ w′ ⊗ ω) ⊗ P)
                             ≤ (zoneOf A₃ w′ ⊗ (ω ⊗ P))
        x-lift w′ = transport (λ q → ((zoneOf A₃ w′ ⊗ ω) ⊗ P) ≤ q)
                              (⊗-assoc (zoneOf A₃ w′) ω P)
                              (≤-refl ((zoneOf A₃ w′ ⊗ ω) ⊗ P))

        ν≤X : (w′ : 𝓑) → pr₁ kν w′ ≤ (zoneOf A₃ w′ ⊗ (ω ⊗ P))
        ν≤X w′ = ≤-trans
                  (≤-trans (⊕-increasing-left (A₂ w′) (pr₁ kν w′))
                           (z-in A₃ w′))
                  (x-≤-x⊗ (zoneOf A₃ w′) (ω ⊗ P)
                    (≤-trans ω-pos (x-≤-x⊗ ω P P+)))

\end{code}

The recursor, assembled.

\begin{code}

GoodH-Iter : GoodH ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι) μ-Iter
GoodH-Iter =
 (λ Tg Ta Tν w → Torbit Tg Ta w ⊕ Tν w)
 , (maps , ((FI , packI) , bndHI))
 , bndL
 where
  bndHI : BndH ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι)
               (λ Tg Ta Tν w → Torbit Tg Ta w ⊕ Tν w) (FI , packI)
  bndHI = λ g kg bndg →
           BndD-Iter g (pr₁ kg) bndg
             (pack-to-Tracked (pr₁ kg) (pr₂ kg))

  maps : (Tg : 𝕋 (ι ⇒ ι)) → LT (ι ⇒ ι) Tg
       → LT (ι ⇒ ι ⇒ ι) (λ Ta Tν w → Torbit Tg Ta w ⊕ Tν w)
  maps Tg (gmaps , kg , bndg) =
   maps₂ , ((IterPack.FI2 kg , IterPack.pack2 kg) , bndH₂)
   where
    trkg : Tracked (pr₁ kg)
    trkg = pack-to-Tracked (pr₁ kg) (pr₂ kg)

    orbitG : (Ta : 𝕋 ι) → GoodT ι Ta → GoodT ι (Torbit Tg Ta)
    orbitG Ta gTa = orbit-goodT Tg gmaps D c M gD cε vM Mε affg Ta gTa
     where
      ex = BndH-to-aff-good Tg kg bndg
      D  = pr₁ ex
      c  = pr₁ (pr₂ ex)
      M  = pr₁ (pr₂ (pr₂ ex))
      gD = pr₁ (pr₂ (pr₂ (pr₂ ex)))
      cε = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ ex))))
      vM = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ ex)))))
      Mε = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ ex))))))
      affg = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ ex))))))

    bndH₂ : BndH (ι ⇒ ι ⇒ ι) (λ Ta Tν w → Torbit Tg Ta w ⊕ Tν w)
                 (IterPack.FI2 kg , IterPack.pack2 kg)
    bndH₂ = BndD-Iter Tg (pr₁ kg) bndg trkg

    maps₂ : (Ta : 𝕋 ι) → GoodT ι Ta
          → LT (ι ⇒ ι) (λ Tν w → Torbit Tg Ta w ⊕ Tν w)
    maps₂ Ta gTa =
     (λ Tν gTν → GoodT-⊕ (Torbit Tg Ta) Tν (orbitG Ta gTa) gTν)
     , (IterPack.FI2 kg (Ta , gTa)
       , bndH₂ Ta (Ta , gTa) (λ w → ≤-refl (Ta w)))

  bndL : (w : 𝓑) → BndL ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι) w
                        (λ Tg Ta Tν w′ → Torbit Tg Ta w′ ⊕ Tν w′) μ-Iter
  bndL w g Tg lTg g-glob a Ta gTa a-glob ν Tν gTν ν-glob =
   ≤-trans (⊕-mono-left (≤-L-mono (λ k → orbit-pt k w)) ν)
           (⊕-mono-right (Torbit Tg Ta w) (ν-glob w))
   where
    orbit-pt : (k : ℕ) (w′ : 𝓑) → iter g a k ≤ iter Tg Ta k w′
    orbit-pt zero     w′ = a-glob w′
    orbit-pt (succ k) w′ =
     g-glob w′ (iter g a k) (iter Tg Ta k)
       (GoodT-iter Tg Ta (pr₁ lTg) gTa k) (λ w″ → orbit-pt k w″)

\end{code}
