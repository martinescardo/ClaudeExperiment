Design H, merged/doubled-budget fork — stage 2b: the rebase, for the
`MultHereditaryHM` predicate.

This is `MultHereditaryH3` retargeted at `MultHereditaryHM` (the `2×`-budget
predicate), the parallel-line record kept alongside the original. The only
substantive difference from `H3` is in the `ZApply-rebase` *arrow* case:
consuming a function-typed argument now threads the doubled budget
`kbudget +ℕ kbudget` through the accumulator (matching `HM.ZApply`). Since
that budget enters the index arithmetic (`I1kh`, `I3kh`) only as an opaque
`ℕ`, the same `+ℕ`/`succ` bookkeeping goes through with the doubled value.

The multiplier core `mult-rebase` here is still the original `I2 ∘ I3`
composition (adequate for the *clean-multiplier* rebases — `packδ`, `packS`).
The function-middle `pack2` leaf, whose source multiplier carries hidden
bumps, needs the over-count-free *merged* core `mult-rebase-merged`
(`MultHereditaryH18Proto`); the merged ground-rebase for that is added
separately below. The conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryHM3
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
        ⊕-increasing-right)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊗-assoc ; ⊕-increasing-left)
open import Claude.BrouwerOrdinals.MultAffine fe using (ω-pos)
open import Claude.BrouwerOrdinals.MultBump fe
 using (bump ; bumpk ; bumpk-mono ; ≤-bump ; ⊗-≤-bump)
open import Claude.DialogueTreeHeight.MultHereditaryH fe
 using (_+ℕ_)
open import Claude.DialogueTreeHeight.MultHereditaryHM fe
 using (𝕂 ; ZApply ; ZCont ; PackDom ; kadd ; kmult ; kbudget)
open import Claude.DialogueTreeHeight.MultHereditaryH2 fe
 using (+ℕ-succ-right ; +ℕ-assoc ; +ℕ-shuffle ;
        bumpk-+ ; ≤-bumpk ; bumpk-pad ;
        B-step ; zdom-ext ; pool-ext ; rbb)

\end{code}

Index padding under a fixed right summand, the multiplier re-basing chain,
and the ground-zone conversion. (Verbatim from `H3`.)

\begin{code}

bumpk-pad-shuffle : (a d J : ℕ) (P : 𝓑)
                  → bumpk (a +ℕ J) P ≤ bumpk ((a +ℕ d) +ℕ J) P
bumpk-pad-shuffle a d J P =
 transport (λ n → bumpk (a +ℕ J) P ≤ bumpk n P)
           (+ℕ-shuffle a J d)
           (bumpk-pad (a +ℕ J) d P)

mult-rebase : (M MH M′ MH′ : 𝓑) (j JH u JH′ e : ℕ)
            → ((M ⊕ MH) ≤ bumpk e (M′ ⊕ MH′))
            → ((P : 𝓑) → bumpk (j +ℕ JH) P ≤ bumpk (u +ℕ JH′) P)
            → bumpk (j +ℕ JH) (M ⊕ MH)
              ≤ bumpk ((u +ℕ e) +ℕ JH′) (M′ ⊕ MH′)
mult-rebase M MH M′ MH′ j JH u JH′ e I2 I3 =
 ≤-trans (I3 (M ⊕ MH))
  (transport (λ n → bumpk (u +ℕ JH′) (M ⊕ MH) ≤ bumpk n (M′ ⊕ MH′))
             (+ℕ-shuffle u JH′ e)
             (transport (λ z → bumpk (u +ℕ JH′) (M ⊕ MH) ≤ z)
                        ((bumpk-+ (u +ℕ JH′) e (M′ ⊕ MH′)) ⁻¹)
                        (bumpk-mono (u +ℕ JH′) I2)))

ground-rebase : (A A′ D D′ : 𝓑 → 𝓑) (MH MH′ : 𝓑) (JH JH′ : ℕ)
                (c c′ M M′ : 𝓑) (j u e : ℕ)
              → ((w : 𝓑) → (D w ⊕ (A w ⊕ c))
                   ≤ ((D′ w ⊕ (A′ w ⊕ c′))
                       ⊗ bumpk ((u +ℕ e) +ℕ JH′) (M′ ⊕ MH′)))
              → ((M ⊕ MH) ≤ bumpk e (M′ ⊕ MH′))
              → ((P : 𝓑) → bumpk (j +ℕ JH) P ≤ bumpk (u +ℕ JH′) P)
              → (V : 𝓑) (w : 𝓑)
              → V ≤ ((D w ⊕ (A w ⊕ c)) ⊗ bumpk (j +ℕ JH) (M ⊕ MH))
              → V ≤ ((D′ w ⊕ (A′ w ⊕ c′))
                      ⊗ bumpk (succ (u +ℕ e) +ℕ JH′) (M′ ⊕ MH′))
ground-rebase A A′ D D′ MH MH′ JH JH′ c c′ M M′ j u e I1 I2 I3 V w hV =
 ≤-trans hV
  (≤-trans (⊗-mono-right (D w ⊕ (A w ⊕ c))
             (mult-rebase M MH M′ MH′ j JH u JH′ e I2 I3))
    (≤-trans (⊗-mono-left (I1 w) B)
      (transport (λ z → z ≤ (Z′ ⊗ bump B)) ((⊗-assoc Z′ B B) ⁻¹)
                 (⊗-mono-right Z′ (⊗-≤-bump B)))))
 where
  B Z′ : 𝓑
  B  = bumpk ((u +ℕ e) +ℕ JH′) (M′ ⊕ MH′)
  Z′ = D′ w ⊕ (A′ w ⊕ c′)

\end{code}

The budget-splitting lemmas for padding `PackDom` components up to the spine
budget. (Verbatim from `H3`.)

\begin{code}

rbb-split : (τ : type) (u e : ℕ)
          → Σ d ꞉ ℕ , rbb τ u e ＝ (succ (u +ℕ e) +ℕ d)
rbb-split ι               u e = 0 , ((+ℕ-zero-right (succ (u +ℕ e))) ⁻¹)
 where
  +ℕ-zero-right : (a : ℕ) → (a +ℕ 0) ＝ a
  +ℕ-zero-right zero     = refl
  +ℕ-zero-right (succ a) = ap succ (+ℕ-zero-right a)
rbb-split (ι ⇒ τ)         u e =
 succ (pr₁ IH) , (pr₂ IH ∙ ((+ℕ-succ-right (succ (u +ℕ e)) (pr₁ IH)) ⁻¹))
 where
  IH : Σ d ꞉ ℕ , rbb τ (succ u) e ＝ (succ (succ (u +ℕ e)) +ℕ d)
  IH = rbb-split τ (succ u) e
rbb-split ((σ₁ ⇒ σ₂) ⇒ τ) u e =
 succ (succ (pr₁ IH))
 , (pr₂ IH′
    ∙ ((+ℕ-succ-right (succ (u +ℕ e)) (succ (pr₁ IH))) ⁻¹))
 where
  IH : Σ d ꞉ ℕ , rbb τ (succ u) (succ e) ＝ (succ (succ u +ℕ succ e) +ℕ d)
  IH = rbb-split τ (succ u) (succ e)

  eq : (succ (succ u +ℕ succ e) +ℕ pr₁ IH)
       ＝ (succ (succ (u +ℕ e)) +ℕ succ (pr₁ IH))
  eq = ap (λ n → succ (succ n) +ℕ pr₁ IH) (+ℕ-succ-right u e)
       ∙ ((+ℕ-succ-right (succ (succ (u +ℕ e))) (pr₁ IH)) ⁻¹)

  IH′ : Σ d ꞉ ℕ , rbb τ (succ u) (succ e)
                   ＝ (succ (succ (u +ℕ e)) +ℕ succ d)
  IH′ = pr₁ IH , (pr₂ IH ∙ eq)

rbb-split-u : (τ : type) (u e : ℕ)
            → Σ d ꞉ ℕ , rbb τ u e ＝ (u +ℕ d)
rbb-split-u τ u e =
 (succ e +ℕ pr₁ s)
 , (pr₂ s
    ∙ ap (_+ℕ pr₁ s) ((+ℕ-succ-right u e) ⁻¹)
    ∙ +ℕ-assoc u (succ e) (pr₁ s))
 where
  s : Σ d ꞉ ℕ , rbb τ u e ＝ (succ (u +ℕ e) +ℕ d)
  s = rbb-split τ u e

\end{code}

The rebase, by mutual induction on the type. The recursive calls' budgets
match `rbb`'s clauses definitionally. Only the `ZApply-rebase` arrow clause
differs from `H3`: the consumed function argument's budget is threaded
doubled (`kbudget +ℕ kbudget`), matching `HM.ZApply`.

\begin{code}

ZCont-rebase
 : (τ : type) (k : 𝕂 τ)
   (A A′ D D′ : 𝓑 → 𝓑) (MH MH′ : 𝓑) (JH JH′ : ℕ)
   (c c′ M M′ : 𝓑) (j u e : ℕ)
 → ((w : 𝓑) → (D w ⊕ (A w ⊕ c))
      ≤ ((D′ w ⊕ (A′ w ⊕ c′)) ⊗ bumpk ((u +ℕ e) +ℕ JH′) (M′ ⊕ MH′)))
 → ((M ⊕ MH) ≤ bumpk e (M′ ⊕ MH′))
 → ((P : 𝓑) → bumpk (j +ℕ JH) P ≤ bumpk (u +ℕ JH′) P)
 → (ω ≤ (M′ ⊕ MH′))
 → ZCont τ k A MH JH D c M j
 → ZCont τ k A′ MH′ JH′ D′ c′ M′ (rbb τ u e)

ZApply-rebase
 : (σ τ : type) (F : 𝕂 σ → 𝕂 τ)
   (A A′ D D′ : 𝓑 → 𝓑) (MH MH′ : 𝓑) (JH JH′ : ℕ)
   (c c′ M M′ : 𝓑) (j u e : ℕ)
 → ((w : 𝓑) → (D w ⊕ (A w ⊕ c))
      ≤ ((D′ w ⊕ (A′ w ⊕ c′)) ⊗ bumpk ((u +ℕ e) +ℕ JH′) (M′ ⊕ MH′)))
 → ((M ⊕ MH) ≤ bumpk e (M′ ⊕ MH′))
 → ((P : 𝓑) → bumpk (j +ℕ JH) P ≤ bumpk (u +ℕ JH′) P)
 → (ω ≤ (M′ ⊕ MH′))
 → ZApply σ τ F A MH JH D c M j
 → ZApply σ τ F A′ MH′ JH′ D′ c′ M′ (rbb (σ ⇒ τ) u e)

ZCont-rebase ι k A A′ D D′ MH MH′ JH JH′ c c′ M M′ j u e I1 I2 I3 I4 z =
 λ w → ground-rebase A A′ D D′ MH MH′ JH JH′ c c′ M M′ j u e
        I1 I2 I3 (pr₁ k w) w (z w)

ZCont-rebase (σ ⇒ τ) k A A′ D D′ MH MH′ JH JH′ c c′ M M′ j u e
             I1 I2 I3 I4 ((pd , pm , pj) , za) =
 (pd′ , pm′ , pj′)
 , ZApply-rebase σ τ (pr₁ k) A A′ D D′ MH MH′ JH JH′ c c′ M M′ j u e
     I1 I2 I3 I4 za
 where
  q : ℕ
  q = rbb (σ ⇒ τ) u e

  pool′ : 𝓑
  pool′ = M′ ⊕ MH′

  spl : Σ d ꞉ ℕ , q ＝ (succ (u +ℕ e) +ℕ d)
  spl = rbb-split (σ ⇒ τ) u e

  splu : Σ d ꞉ ℕ , q ＝ (u +ℕ d)
  splu = rbb-split-u (σ ⇒ τ) u e

  pad-succ : bumpk (succ (u +ℕ e) +ℕ JH′) pool′ ≤ bumpk (q +ℕ JH′) pool′
  pad-succ =
   transport (λ n → bumpk (succ (u +ℕ e) +ℕ JH′) pool′
                     ≤ bumpk (n +ℕ JH′) pool′)
             ((pr₂ spl) ⁻¹)
             (bumpk-pad-shuffle (succ (u +ℕ e)) (pr₁ spl) JH′ pool′)

  pd′ : (w : 𝓑) → kadd σ τ k w
                   ≤ ((D′ w ⊕ (A′ w ⊕ c′)) ⊗ bumpk (q +ℕ JH′) pool′)
  pd′ w = ≤-trans
           (ground-rebase A A′ D D′ MH MH′ JH JH′ c c′ M M′ j u e
             I1 I2 I3 (kadd σ τ k w) w (pd w))
           (⊗-mono-right (D′ w ⊕ (A′ w ⊕ c′)) pad-succ)

  pm′ : kmult σ τ k ≤ bumpk (q +ℕ JH′) pool′
  pm′ = ≤-trans (pm)
         (≤-trans (mult-rebase M MH M′ MH′ j JH u JH′ e I2 I3)
           (transport (λ n → bumpk ((u +ℕ e) +ℕ JH′) pool′
                              ≤ bumpk (n +ℕ JH′) pool′)
                      (eq2 ⁻¹)
                      (bumpk-pad-shuffle (u +ℕ e) (succ (pr₁ spl)) JH′
                                         pool′)))
   where
    eq2 : q ＝ ((u +ℕ e) +ℕ succ (pr₁ spl))
    eq2 = pr₂ spl ∙ ((+ℕ-succ-right (u +ℕ e) (pr₁ spl)) ⁻¹)

  pj′ : (P : 𝓑) → bumpk (kbudget σ τ k) P ≤ bumpk (q +ℕ JH′) P
  pj′ P = ≤-trans (pj P)
           (≤-trans (I3 P)
             (transport (λ n → bumpk (u +ℕ JH′) P ≤ bumpk (n +ℕ JH′) P)
                        ((pr₂ splu) ⁻¹)
                        (bumpk-pad-shuffle u (pr₁ splu) JH′ P)))

ZApply-rebase ι τ F A A′ D D′ MH MH′ JH JH′ c c′ M M′ j u e
              I1 I2 I3 I4 za =
 λ b → ZCont-rebase τ (F b)
        (λ w → A w ⊕ pr₁ b w) (λ w → A′ w ⊕ pr₁ b w)
        D D′ MH MH′ JH JH′ c c′ M M′ j (succ u) e
        (I1b b) I2 I3′ I4 (za b)
 where
  I3′ : (P : 𝓑) → bumpk (j +ℕ JH) P ≤ bumpk (succ u +ℕ JH′) P
  I3′ P = ≤-trans (I3 P) (≤-bump (bumpk (u +ℕ JH′) P))
  B : 𝓑
  B = bumpk ((u +ℕ e) +ℕ JH′) (M′ ⊕ MH′)

  B+ : S Z ≤ B
  B+ = ≤-trans (≤-trans ω-pos I4) (≤-bumpk ((u +ℕ e) +ℕ JH′) (M′ ⊕ MH′))

  I1b : (b : 𝕂 ι) (w : 𝓑)
      → (D w ⊕ ((A w ⊕ pr₁ b w) ⊕ c))
        ≤ ((D′ w ⊕ ((A′ w ⊕ pr₁ b w) ⊕ c′))
            ⊗ bumpk ((succ u +ℕ e) +ℕ JH′) (M′ ⊕ MH′))
  I1b b w = ≤-trans
             (zdom-ext D D′ A A′ (λ w′ → pr₁ b w′) c c′ B B+ I1 w)
             (⊗-mono-right (D′ w ⊕ ((A′ w ⊕ pr₁ b w) ⊕ c′))
               (B-step ((u +ℕ e) +ℕ JH′) (M′ ⊕ MH′) I4))

ZApply-rebase (σ₁ ⇒ σ₂) τ F A A′ D D′ MH MH′ JH JH′ c c′ M M′ j u e
              I1 I2 I3 I4 za =
 λ kh → ZCont-rebase τ (F kh)
         (λ w → A w ⊕ kadd σ₁ σ₂ kh w) (λ w → A′ w ⊕ kadd σ₁ σ₂ kh w)
         D D′
         (MH ⊕ kmult σ₁ σ₂ kh) (MH′ ⊕ kmult σ₁ σ₂ kh)
         (JH +ℕ (kbudget σ₁ σ₂ kh +ℕ kbudget σ₁ σ₂ kh))
         (JH′ +ℕ (kbudget σ₁ σ₂ kh +ℕ kbudget σ₁ σ₂ kh))
         c c′ M M′ j (succ u) (succ e)
         (I1kh kh) (I2kh kh) (I3kh kh) (I4kh kh) (za kh)
 where
  pool′ : 𝓑
  pool′ = M′ ⊕ MH′

  B : 𝓑
  B = bumpk ((u +ℕ e) +ℕ JH′) pool′

  B+ : S Z ≤ B
  B+ = ≤-trans (≤-trans ω-pos I4) (≤-bumpk ((u +ℕ e) +ℕ JH′) pool′)

  I4kh : (kh : 𝕂 (σ₁ ⇒ σ₂)) → ω ≤ (M′ ⊕ (MH′ ⊕ kmult σ₁ σ₂ kh))
  I4kh kh = ≤-trans I4
             (⊕-mono-right M′ (⊕-increasing-right MH′ (kmult σ₁ σ₂ kh)))

  I2kh : (kh : 𝕂 (σ₁ ⇒ σ₂))
       → (M ⊕ (MH ⊕ kmult σ₁ σ₂ kh))
         ≤ bumpk (succ e) (M′ ⊕ (MH′ ⊕ kmult σ₁ σ₂ kh))
  I2kh kh =
   transport (λ z → z ≤ bumpk (succ e) (M′ ⊕ (MH′ ⊕ mh)))
             (⊕-assoc M MH mh)
             (transport (λ z → ((M ⊕ MH) ⊕ mh) ≤ z)
                        (ap (bumpk (succ e)) (⊕-assoc M′ MH′ mh))
                        (pool-ext (M ⊕ MH) (M′ ⊕ MH′) mh e I4 I2))
   where
    mh : 𝓑
    mh = kmult σ₁ σ₂ kh

  I3kh : (kh : 𝕂 (σ₁ ⇒ σ₂)) (P : 𝓑)
       → bumpk (j +ℕ (JH +ℕ (kbudget σ₁ σ₂ kh +ℕ kbudget σ₁ σ₂ kh))) P
         ≤ bumpk (succ u +ℕ (JH′ +ℕ (kbudget σ₁ σ₂ kh +ℕ kbudget σ₁ σ₂ kh)))
                 P
  I3kh kh P =
   transport (λ z → z ≤ bumpk (succ (u +ℕ (JH′ +ℕ kb))) P)
             (eq-l ⁻¹) core
   where
    kb : ℕ
    kb = kbudget σ₁ σ₂ kh +ℕ kbudget σ₁ σ₂ kh

    eq-l : bumpk (j +ℕ (JH +ℕ kb)) P ＝ bumpk (j +ℕ JH) (bumpk kb P)
    eq-l = ap (λ n → bumpk n P) ((+ℕ-assoc j JH kb) ⁻¹)
           ∙ bumpk-+ (j +ℕ JH) kb P

    eq-r : bumpk (u +ℕ JH′) (bumpk kb P) ＝ bumpk (u +ℕ (JH′ +ℕ kb)) P
    eq-r = ((bumpk-+ (u +ℕ JH′) kb P) ⁻¹)
           ∙ ap (λ n → bumpk n P) (+ℕ-assoc u JH′ kb)

    core : bumpk (j +ℕ JH) (bumpk kb P)
           ≤ bumpk (succ (u +ℕ (JH′ +ℕ kb))) P
    core = ≤-trans (I3 (bumpk kb P))
            (transport
              (λ z → z ≤ bumpk (succ (u +ℕ (JH′ +ℕ kb))) P)
              (eq-r ⁻¹)
              (≤-bump (bumpk (u +ℕ (JH′ +ℕ kb)) P)))

  I1kh : (kh : 𝕂 (σ₁ ⇒ σ₂)) (w : 𝓑)
       → (D w ⊕ ((A w ⊕ kadd σ₁ σ₂ kh w) ⊕ c))
         ≤ ((D′ w ⊕ ((A′ w ⊕ kadd σ₁ σ₂ kh w) ⊕ c′))
             ⊗ bumpk ((succ u +ℕ succ e)
                        +ℕ (JH′ +ℕ (kbudget σ₁ σ₂ kh +ℕ kbudget σ₁ σ₂ kh)))
                     (M′ ⊕ (MH′ ⊕ kmult σ₁ σ₂ kh)))
  I1kh kh w =
   ≤-trans
    (zdom-ext D D′ A A′ (kadd σ₁ σ₂ kh) c c′ B B+ I1 w)
    (⊗-mono-right (D′ w ⊕ ((A′ w ⊕ kadd σ₁ σ₂ kh w) ⊕ c′))
      (≤-trans (B-step ((u +ℕ e) +ℕ JH′) pool′ I4)
        (≤-trans
          (bumpk-mono (succ ((u +ℕ e) +ℕ JH′))
            (⊕-mono-right M′ (⊕-increasing-right MH′ mh)))
          (transport
            (λ n → bumpk (succ ((u +ℕ e) +ℕ JH′)) (M′ ⊕ (MH′ ⊕ mh))
                    ≤ bumpk n (M′ ⊕ (MH′ ⊕ mh)))
            E
            (bumpk-pad (succ ((u +ℕ e) +ℕ JH′)) (succ kb)
                       (M′ ⊕ (MH′ ⊕ mh)))))))
   where
    mh : 𝓑
    mh = kmult σ₁ σ₂ kh

    kb : ℕ
    kb = kbudget σ₁ σ₂ kh +ℕ kbudget σ₁ σ₂ kh

    E : (succ ((u +ℕ e) +ℕ JH′) +ℕ succ kb)
        ＝ ((succ u +ℕ succ e) +ℕ (JH′ +ℕ kb))
    E = +ℕ-succ-right (succ ((u +ℕ e) +ℕ JH′)) kb
        ∙ ap (λ n → succ (succ n)) (+ℕ-assoc (u +ℕ e) JH′ kb)
        ∙ ap (λ n → succ (n +ℕ (JH′ +ℕ kb))) ((+ℕ-succ-right u e) ⁻¹)

\end{code}

The *merged* ground leaf rebase — for the function-middle `pack2`, whose
source multiplier carries hidden bumps that the raw pool hypothesis `I2` of
`ground-rebase` cannot absorb at constant slack. Here the caller supplies the
combined multiplier domination `hMult` directly (proved via the prototype's
`mult-rebase-merged` + `mult-absorb`, folding the bumps into the budget
index), and the zone `I1` at the same target index `J`; the two factors merge
by `⊗-≤-bump` into a single `bump`, exactly as in `ground-rebase`. No `I2`,
no over-count.

\begin{code}

ground-rebase-merged
 : (A A′ D D′ : 𝓑 → 𝓑) (c c′ Msrc Mtgt : 𝓑) (jsrc J : ℕ)
 → ((w : 𝓑) → (D w ⊕ (A w ⊕ c))
      ≤ ((D′ w ⊕ (A′ w ⊕ c′)) ⊗ bumpk J Mtgt))
 → (bumpk jsrc Msrc ≤ bumpk J Mtgt)
 → (V w : 𝓑)
 → V ≤ ((D w ⊕ (A w ⊕ c)) ⊗ bumpk jsrc Msrc)
 → V ≤ ((D′ w ⊕ (A′ w ⊕ c′)) ⊗ bumpk (succ J) Mtgt)
ground-rebase-merged A A′ D D′ c c′ Msrc Mtgt jsrc J I1 hMult V w hV =
 ≤-trans hV
  (≤-trans (⊗-mono-right (D w ⊕ (A w ⊕ c)) hMult)
    (≤-trans (⊗-mono-left (I1 w) B)
      (transport (λ z → z ≤ (Z′ ⊗ bump B)) ((⊗-assoc Z′ B B) ⁻¹)
                 (⊗-mono-right Z′ (⊗-≤-bump B)))))
 where
  B Z′ : 𝓑
  B  = bumpk J Mtgt
  Z′ = D′ w ⊕ (A′ w ⊕ c′)

\end{code}
