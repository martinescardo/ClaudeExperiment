The all-ground-`S`-complete fundamental theorem: unconditional `height < ε₀`
for a fragment `T₃` with the ground-`S` diagonal at *every* result type —
the whole `Affₙ` ladder in one predicate, via the type-level zone calculus
of `MultHereditaryFAffN`.

The refinement here is uniform: a transformer whose type has a *ground
domain* carries the full joint bound, `ExtraN ι τ = JAff (ι ⇒ τ)`, and an
arrow domain carries nothing. (Contrast `MultHereditaryFT`, codomain-first
and data only at `ι ⇒ ι`, and `MultHereditaryFJT`, data at `ι ⇒ ι` and
`ι ⇒ ι ⇒ ι`.) Since `JAff` itself collapses past a function argument, the
data is substantive exactly on all-ground prefixes and trivially
dischargeable elsewhere — so a *single* pair of clauses suffices and the
`K`/`S` obligations reduce at abstract types by the domain split alone.

The fragment `T₃` has `Ω/Zero/Succ/Iter/K/·` and three `S` families:

* `Sg₃ {τ}` — shared argument `ι`, middle `ι`, **any** result type `τ`:
  the diagonal is `JAff-Sg-diag`, closing at one stroke every rung of the
  arity ladder (`τ = ι` is `T★`'s `Sg★`; `τ = ι ⇒ ι` is the family
  `MultHereditaryFJT` documented as needing `Aff₃`; and so on), plus all
  mixed types `τ`;
* `Sh₃` — shared argument function-typed (= `T★`'s `Sh★`), any `σ , τ`;
* `Sx₃ {σ} {τ}` — shared argument `ι`, **any** middle `σ`, and a
  `Collapses τ` witness (some argument of `τ` is function-typed): the
  diagonal's obligation is then trivially dischargeable.

So `T₃ ⊇ T★` (embedding `emb★`, coherent over the `T₁` semantics), strictly
— and `T₃` contains all-ground `S` at every arity, beyond both `T⁺` and
`T₂`. Honest scope: the `S` family still outside is shared argument `ι`,
*function-typed middle* `σ`, and *all-ground* `τ` — there the diagonal
needs real joint data that would have to depend on the function argument's
own data (Howard's transformer tower). Note the fragments are genuinely
incomparable at that frontier: `T⁺`/`T₂` contain some such instances
precisely because their coarser predicates demand no data at the diagonal's
type, while `T₃`'s finer predicate (which is what buys every all-ground
`S`) demands data there that cannot be produced. A single predicate cannot
have both; their join is the transformer-tower step. The conjecture for
full System T remains open — also outside everything here are the
super-linear transformers.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryFNT
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import UF.Base using (ap₂)
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import EffectfulForcing.MFPSAndVariations.Dialogue using (generic)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe using (⊕-mono-left)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; S-<-ε₀ ; ⊕-mono-right)
open import Claude.BrouwerOrdinals.AffineClosure fe using (Z<ε₀)
open import Claude.DialogueTreeHeight.Majorant fe
 using (Maj ; μ-Zero ; μ-Succ ; μ-Ω ; μ-K ; μ-S ; μ-Iter ;
        T₁ ; Ω₁ ; Zero₁ ; Succ₁ ; Iter₁ ; K₁ ; S₁ ; _·₁_ ; ⟦_⟧₁ ; μ ;
        height-≤-μ)
open import Claude.DialogueTreeHeight.MultHereditaryF fe
 using (𝕋 ; GoodT ; Torbit ; GoodT-iter ; GoodT-⊕)
open import Claude.DialogueTreeHeight.MultHereditaryFAff fe
 using (orbit-good-aff)
open import Claude.DialogueTreeHeight.MultHereditaryFAffN fe
 using (JAff ; Collapses ; JAff-collapse ; JAff-id ; JAff-S ; JAff-const ;
        JAff-add ; JAff-K-outer ; JAff-insert ; JAff-to-AffBounded ;
        JAff-Iter ; JAff-Sg-diag)
open import Claude.DialogueTreeHeight.MultHereditaryT fe
 using (T★ ; Ω★ ; Zero★ ; Succ★ ; Iter★ ; K★ ; Sg★ ; Sh★ ; _·★_)
 renaming (e to e★)

\end{code}

The refined predicate: one clause pair — ground domains carry the joint
bound, arrow domains carry nothing.

\begin{code}

ExtraN : (σ τ : type) → 𝕋 (σ ⇒ τ) → 𝓤₀ ̇
ExtraN ι         τ T = JAff (ι ⇒ τ) T
ExtraN (σ₁ ⇒ σ₂) τ T = 𝟙

LN : (σ : type) → 𝕋 σ → 𝓤₀ ̇
LN ι       T = GoodT ι T
LN (σ ⇒ τ) T = ((Tg : 𝕋 σ) → LN σ Tg → LN τ (T Tg)) × ExtraN σ τ T

BndN : (σ : type) → 𝓑 → 𝕋 σ → Maj σ → 𝓤₀ ̇
BndN ι       w T a = a ≤ T w
BndN (σ ⇒ τ) w T φ = (g : Maj σ) (Tg : 𝕋 σ) → LN σ Tg
                   → ((w′ : 𝓑) → BndN σ w′ Tg g) → BndN τ w (T Tg) (φ g)

GoodN : (σ : type) → Maj σ → 𝓤₀ ̇
GoodN σ φ = Σ T ꞉ 𝕋 σ , LN σ T × ((w : 𝓑) → BndN σ w T φ)

\end{code}

Ground extraction, base combinators, application.

\begin{code}

GoodN-ι-to-<ε₀ : (a : 𝓑) → GoodN ι a → a < ε₀
GoodN-ι-to-<ε₀ a (T , (Tpres , Tmono) , bnd) =
 ≤-trans (≤-S (bnd Z)) (Tpres Z Z<ε₀)

GoodN-Zero : GoodN ι μ-Zero
GoodN-Zero =
 (λ w → w) , ((λ w w<ε₀ → w<ε₀) , (λ w w′ w≤w′ → w≤w′)) , (λ w → ≤-Z)

GoodN-Succ : GoodN (ι ⇒ ι) μ-Succ
GoodN-Succ =
 (λ Tg → Tg) , ((λ Tg gTg → gTg) , JAff-id) , (λ w g Tg gTg gg → gg w)

GoodN-Ω : GoodN (ι ⇒ ι) μ-Ω
GoodN-Ω =
 (λ Tg w → S (Tg w))
 , ((λ Tg (gp , gm) → (λ w w<ε₀ → S-<-ε₀ (Tg w) (gp w w<ε₀))
                    , (λ w w′ w≤w′ → ≤-S (gm w w′ w≤w′)))
   , JAff-S)
 , (λ w g Tg gTg gg → ≤-S (gg w))

GoodN-app : (σ τ : type) (F : Maj (σ ⇒ τ)) (G : Maj σ)
          → GoodN (σ ⇒ τ) F → GoodN σ G → GoodN τ (F G)
GoodN-app σ τ F G (TF , (mF , _) , bF) (TG , lG , bG) =
 TF TG , mF TG lG , (λ w → bF w G TG lG bG)

\end{code}

`K`. The outer projection is `JAff-K-outer` (already type-cased in the
calculus module); the inner constant splits by the shape of `σ`: at `ι` it
is the constant embedding, at `ι ⇒ σ′` a dead-argument insertion of the
argument's own data, past a function argument a collapse.

\begin{code}

extraN-K-outer : (σ τ : type) → ExtraN σ (τ ⇒ σ) (λ Ta Tb → Ta)
extraN-K-outer ι         τ = JAff-K-outer τ
extraN-K-outer (σ₁ ⇒ σ₂) τ = ⋆

extraN-K-inner : (σ τ : type) (Ta : 𝕋 σ) → LN σ Ta → ExtraN τ σ (λ Tb → Ta)
extraN-K-inner ι                σ@ι          Ta gTa = JAff-const Ta gTa
extraN-K-inner (ι ⇒ σ′)         ι            Ta lTa =
 JAff-insert (ι ⇒ σ′) Ta (pr₂ lTa)
extraN-K-inner ((σ₁ ⇒ σ₂) ⇒ σ′) ι            Ta lTa =
 JAff-collapse (ι ⇒ ((σ₁ ⇒ σ₂) ⇒ σ′)) ⋆ (λ Tb → Ta)
extraN-K-inner ι                (τ₁ ⇒ τ₂)    Ta lTa = ⋆
extraN-K-inner (ι ⇒ σ′)         (τ₁ ⇒ τ₂)    Ta lTa = ⋆
extraN-K-inner ((σ₁ ⇒ σ₂) ⇒ σ′) (τ₁ ⇒ τ₂)    Ta lTa = ⋆

GoodN-K : {σ τ : type} → GoodN (σ ⇒ τ ⇒ σ) μ-K
GoodN-K {σ} {τ} =
 (λ Ta Tb → Ta)
 , ((λ Ta lTa → (λ Tb lTb → lTa) , extraN-K-inner σ τ Ta lTa)
   , extraN-K-outer σ τ)
 , (λ w a Ta lTa a-glob b Tb lTb b-glob → a-glob w)

\end{code}

The recursor — unconditional; the argument's `ExtraN ι ι` *is*
`JAff (ι ⇒ ι)`, converted for the orbit engine.

\begin{code}

GoodN-Iter : GoodN ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι) μ-Iter
GoodN-Iter = (λ Tg Ta Tν w → Torbit Tg Ta w ⊕ Tν w) , lI , bnd
 where
  orbitGood : (Tg : 𝕋 (ι ⇒ ι)) → LN (ι ⇒ ι) Tg → (Ta : 𝕋 ι) → GoodT ι Ta
            → GoodT ι (Torbit Tg Ta)
  orbitGood Tg (gTg , jTg) Ta gTa =
   orbit-good-aff Tg gTg (JAff-to-AffBounded Tg jTg) Ta gTa

  lI : LN ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι) (λ Tg Ta Tν w → Torbit Tg Ta w ⊕ Tν w)
  lI = (λ Tg lTg →
         ((λ Ta gTa →
            ((λ Tν gTν → GoodT-⊕ (Torbit Tg Ta) Tν (orbitGood Tg lTg Ta gTa) gTν)
             , JAff-add (Torbit Tg Ta) (orbitGood Tg lTg Ta gTa)))
          , JAff-Iter Tg (JAff-to-AffBounded Tg (pr₂ lTg))))
       , ⋆

  bnd : (w : 𝓑) → BndN ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι) w
                       (λ Tg Ta Tν w → Torbit Tg Ta w ⊕ Tν w) μ-Iter
  bnd w g Tg lTg g-glob a Ta gTa a-glob ν Tν gTν ν-glob =
   ≤-trans (⊕-mono-left (≤-L-mono (λ k → orbit-pt k w)) ν)
           (⊕-mono-right (Torbit Tg Ta w) (ν-glob w))
   where
    orbit-pt : (k : ℕ) (w′ : 𝓑) → iter g a k ≤ iter Tg Ta k w′
    orbit-pt zero     w′ = a-glob w′
    orbit-pt (succ k) w′ =
     g-glob w′ (iter g a k) (iter Tg Ta k)
       (GoodT-iter Tg Ta (pr₁ lTg) gTa k) (λ w″ → orbit-pt k w″)

\end{code}

The three `S` families. All share the transformer and the `BndN` proof
(Design F verbatim); they differ only at the diagonal's `ExtraN` obligation:
`JAff-Sg-diag` for `Sg` (any `τ`), trivial for `Sh` (arrow domain), a
collapse for `Sx` (witnessed).

\begin{code}

GoodN-Sg : {τ : type} → GoodN ((ι ⇒ ι ⇒ τ) ⇒ (ι ⇒ ι) ⇒ ι ⇒ τ) μ-S
GoodN-Sg {τ} =
 (λ Tφ Tγ Ta → (Tφ Ta) (Tγ Ta))
 , ((λ Tφ lTφ →
      ((λ Tγ lTγ →
         ((λ Ta gTa → pr₁ (pr₁ lTφ Ta gTa) (Tγ Ta) (pr₁ lTγ Ta gTa))
          , JAff-Sg-diag τ Tφ Tγ (pr₂ lTφ) (pr₂ lTγ)))
       , ⋆))
    , ⋆)
 , bndS
 where
  bndS : (w : 𝓑)
       → BndN ((ι ⇒ ι ⇒ τ) ⇒ (ι ⇒ ι) ⇒ ι ⇒ τ) w
              (λ Tφ Tγ Ta → (Tφ Ta) (Tγ Ta)) μ-S
  bndS w φ Tφ lTφ φ-glob γ Tγ lTγ γ-glob a Ta lTa a-glob =
   φ-glob w a Ta lTa a-glob (γ a) (Tγ Ta) (pr₁ lTγ Ta lTa)
     (λ w′ → γ-glob w′ a Ta lTa a-glob)

GoodN-Sh : {ρ₁ ρ₂ σ τ : type}
         → GoodN (((ρ₁ ⇒ ρ₂) ⇒ σ ⇒ τ) ⇒ ((ρ₁ ⇒ ρ₂) ⇒ σ) ⇒ (ρ₁ ⇒ ρ₂) ⇒ τ) μ-S
GoodN-Sh {ρ₁} {ρ₂} {σ} {τ} =
 (λ Tφ Tγ Ta → (Tφ Ta) (Tγ Ta))
 , ((λ Tφ lTφ →
      ((λ Tγ lTγ →
         ((λ Ta lTa → pr₁ (pr₁ lTφ Ta lTa) (Tγ Ta) (pr₁ lTγ Ta lTa))
          , ⋆))
       , ⋆))
    , ⋆)
 , bndS
 where
  bndS : (w : 𝓑)
       → BndN (((ρ₁ ⇒ ρ₂) ⇒ σ ⇒ τ) ⇒ ((ρ₁ ⇒ ρ₂) ⇒ σ) ⇒ (ρ₁ ⇒ ρ₂) ⇒ τ) w
              (λ Tφ Tγ Ta → (Tφ Ta) (Tγ Ta)) μ-S
  bndS w φ Tφ lTφ φ-glob γ Tγ lTγ γ-glob a Ta lTa a-glob =
   φ-glob w a Ta lTa a-glob (γ a) (Tγ Ta) (pr₁ lTγ Ta lTa)
     (λ w′ → γ-glob w′ a Ta lTa a-glob)

GoodN-Sx : {σ τ : type} → Collapses τ
         → GoodN ((ι ⇒ σ ⇒ τ) ⇒ (ι ⇒ σ) ⇒ ι ⇒ τ) μ-S
GoodN-Sx {σ} {τ} cw =
 (λ Tφ Tγ Ta → (Tφ Ta) (Tγ Ta))
 , ((λ Tφ lTφ →
      ((λ Tγ lTγ →
         ((λ Ta gTa → pr₁ (pr₁ lTφ Ta gTa) (Tγ Ta) (pr₁ lTγ Ta gTa))
          , JAff-collapse (ι ⇒ τ) cw (λ Ta → (Tφ Ta) (Tγ Ta))))
       , ⋆))
    , ⋆)
 , bndS
 where
  bndS : (w : 𝓑)
       → BndN ((ι ⇒ σ ⇒ τ) ⇒ (ι ⇒ σ) ⇒ ι ⇒ τ) w
              (λ Tφ Tγ Ta → (Tφ Ta) (Tγ Ta)) μ-S
  bndS w φ Tφ lTφ φ-glob γ Tγ lTγ γ-glob a Ta lTa a-glob =
   φ-glob w a Ta lTa a-glob (γ a) (Tγ Ta) (pr₁ lTγ Ta lTa)
     (λ w′ → γ-glob w′ a Ta lTa a-glob)

\end{code}

The fragment `T₃`, its embedding into `T₁`, and the embedding of `T★`.

\begin{code}

data T₃ : type → 𝓤₀ ̇ where
 Ω₃    : T₃ (ι ⇒ ι)
 Zero₃ : T₃ ι
 Succ₃ : T₃ (ι ⇒ ι)
 Iter₃ : T₃ ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι)
 K₃    : {σ τ : type} → T₃ (σ ⇒ τ ⇒ σ)
 Sg₃   : {τ : type} → T₃ ((ι ⇒ ι ⇒ τ) ⇒ (ι ⇒ ι) ⇒ ι ⇒ τ)
 Sh₃   : {ρ₁ ρ₂ σ τ : type}
       → T₃ (((ρ₁ ⇒ ρ₂) ⇒ σ ⇒ τ) ⇒ ((ρ₁ ⇒ ρ₂) ⇒ σ) ⇒ (ρ₁ ⇒ ρ₂) ⇒ τ)
 Sx₃   : {σ τ : type} → Collapses τ
       → T₃ ((ι ⇒ σ ⇒ τ) ⇒ (ι ⇒ σ) ⇒ ι ⇒ τ)
 _·₃_  : {σ τ : type} → T₃ (σ ⇒ τ) → T₃ σ → T₃ τ

infixl 6 _·₃_

e : {σ : type} → T₃ σ → T₁ σ
e Ω₃        = Ω₁
e Zero₃     = Zero₁
e Succ₃     = Succ₁
e Iter₃     = Iter₁
e K₃        = K₁
e Sg₃       = S₁
e Sh₃       = S₁
e (Sx₃ cw)  = S₁
e (t ·₃ u)  = e t ·₁ e u

emb★ : {σ : type} → T★ σ → T₃ σ
emb★ Ω★        = Ω₃
emb★ Zero★     = Zero₃
emb★ Succ★     = Succ₃
emb★ Iter★     = Iter₃
emb★ K★        = K₃
emb★ Sg★       = Sg₃ {ι}
emb★ Sh★       = Sh₃
emb★ (t ·★ u)  = emb★ t ·₃ emb★ u

emb★-coherent : {σ : type} (t : T★ σ) → e (emb★ t) ＝ e★ t
emb★-coherent Ω★        = refl
emb★-coherent Zero★     = refl
emb★-coherent Succ★     = refl
emb★-coherent Iter★     = refl
emb★-coherent K★        = refl
emb★-coherent Sg★       = refl
emb★-coherent Sh★       = refl
emb★-coherent (t ·★ u)  = ap₂ _·₁_ (emb★-coherent t) (emb★-coherent u)

\end{code}

The fundamental theorem and its payoffs, unconditional.

\begin{code}

goodμ : {σ : type} (t : T₃ σ) → GoodN σ (μ (e t))
goodμ Ω₃        = GoodN-Ω
goodμ Zero₃     = GoodN-Zero
goodμ Succ₃     = GoodN-Succ
goodμ Iter₃     = GoodN-Iter
goodμ (K₃ {σ} {τ}) = GoodN-K {σ} {τ}
goodμ (Sg₃ {τ}) = GoodN-Sg {τ}
goodμ (Sh₃ {ρ₁} {ρ₂} {σ} {τ}) = GoodN-Sh {ρ₁} {ρ₂} {σ} {τ}
goodμ (Sx₃ {σ} {τ} cw) = GoodN-Sx {σ} {τ} cw
goodμ (t ·₃ u)  = GoodN-app _ _ (μ (e t)) (μ (e u)) (goodμ t) (goodμ u)

μ-<-ε₀ : (t : T₃ ι) → μ (e t) < ε₀
μ-<-ε₀ t = GoodN-ι-to-<ε₀ (μ (e t)) (goodμ t)

height-<-ε₀ : (t : T₃ ι) → height ⟦ e t ⟧₁ < ε₀
height-<-ε₀ t = ≤-trans (≤-S (height-≤-μ (e t))) (μ-<-ε₀ t)

dialogue-height-<-ε₀ : (t : T₃ ((ι ⇒ ι) ⇒ ι))
                     → height (⟦ e t ⟧₁ generic) < ε₀
dialogue-height-<-ε₀ t = height-<-ε₀ (t ·₃ Ω₃)

\end{code}
