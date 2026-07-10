The joint fundamental theorem: unconditional `height < ε₀` for a Design-F
fragment containing `MultHereditaryT`'s `T★` — in particular the all-ground
`S` — *and* the function-typed ground-`S` families of `MultHereditaryFT`.

`MultHereditaryFT`'s refinement carries affine data only at `ι ⇒ ι`, so its
fragment `T⁺` misses `T★`'s all-ground instance `Sg★`. Here the refinement is
extended one rung up the arity ladder: transformers of type `ι ⇒ ι ⇒ ι` carry
the *binary joint* bound `Aff₂` of `MultHereditaryFAff2`,

  `Extra ι ι = AffBounded`, `Extra ι (ι ⇒ ι) = Aff₂`, trivial elsewhere,

with `Extra` matching the domain first (an arrow domain has no obligation
regardless of the codomain — which is what lets the function-typed `S`
families reduce at abstract types; the price is that a *ground* domain must
see the codomain's shape, so those families split by that shape). The
predicate `LJ`/`BndJ`/`GoodJ` is otherwise `MultHereditaryF` verbatim, and
the refinement is paid at the `MultHereditaryFAff`/`FAff2` lemmas:
`Succ/Ω/K/Iter` as in `MultHereditaryFT` plus the new joint obligations —
`K`'s outer partial application (`Aff₂-K`), `K` at `σ = ι ⇒ ι` producing a
constant binary functional (`Aff₂-insert`), the recursor's two ground
arguments jointly (`Aff₂-Iter`), and — the point of the exercise — the
all-ground `S` diagonal (`AffBounded-Sg-diag`). **Both the recursor and the
all-ground `S` are unconditional in this predicate.**

The fragment `T₂` has `Ω/Zero/Succ/Iter/K/·` and *four* `S` families:
`Sg₂` (all-ground, = `T★`'s `Sg★`), `Sh₂` (shared argument function-typed,
= `T★`'s `Sh★`), and the two function-typed splittings of `MultHereditaryFT`'s
`Sf⁺` — `Sfh₂` (middle result type a function) and `Sfr₂` (result
`ι ⇒ κ₁ ⇒ κ₂`). So `T₂ ⊇ T★` (witnessed by the embedding `emb★`), strictly:
`Sfh₂`/`Sfr₂` are outside `T★`'s families. Honest scope: `T₂` misses exactly
one `T⁺` instance family — `Sf⁺` at result type `ι ⇒ ι` (an `S` whose
diagonal is an all-ground *binary* function): its obligation is an `Aff₂`
that would have to come from *ternary* joint data on `φ : ι ⇒ σ ⇒ ι ⇒ ι ⇒ ι`
which `Extra` does not carry. That is the next rung (`Aff₃`, and in general
the `n`-ary zone calculus); each rung is the same arithmetic one arity up,
but the ladder has no uniform top here. Also still outside: ground-`S` with
function-typed middle and ground result (affine data depending on the
function argument's data — Howard's transformer tower), and everything
super-linear. The conjecture for full System T remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryFJT
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
 using (AffBounded ; AffBounded-id ; AffBounded-S ; AffBounded-const ;
        AffBounded-add ; orbit-good-aff)
open import Claude.DialogueTreeHeight.MultHereditaryFAff2 fe
 using (Aff₂ ; Aff₂-K ; Aff₂-insert ; Aff₂-Iter ; AffBounded-Sg-diag)
open import Claude.DialogueTreeHeight.MultHereditaryT fe
 using (T★ ; Ω★ ; Zero★ ; Succ★ ; Iter★ ; K★ ; Sg★ ; Sh★ ; _·★_)
 renaming (e to e★)

\end{code}

The refined predicate. `Extra` matches the domain first: an arrow domain
carries nothing (reducing at abstract codomains); a ground domain carries
`AffBounded` at codomain `ι`, `Aff₂` at codomain `ι ⇒ ι`, nothing above.

\begin{code}

Extra : (σ τ : type) → 𝕋 (σ ⇒ τ) → 𝓤₀ ̇
Extra ι         ι                     T = AffBounded T
Extra ι         (ι ⇒ ι)               T = Aff₂ T
Extra ι         (ι ⇒ (τ₁ ⇒ τ₂))       T = 𝟙
Extra ι         ((τ₁ ⇒ τ₂) ⇒ τ₃)      T = 𝟙
Extra (σ₁ ⇒ σ₂) τ                     T = 𝟙

LJ : (σ : type) → 𝕋 σ → 𝓤₀ ̇
LJ ι       T = GoodT ι T
LJ (σ ⇒ τ) T = ((Tg : 𝕋 σ) → LJ σ Tg → LJ τ (T Tg)) × Extra σ τ T

BndJ : (σ : type) → 𝓑 → 𝕋 σ → Maj σ → 𝓤₀ ̇
BndJ ι       w T a = a ≤ T w
BndJ (σ ⇒ τ) w T φ = (g : Maj σ) (Tg : 𝕋 σ) → LJ σ Tg
                   → ((w′ : 𝓑) → BndJ σ w′ Tg g) → BndJ τ w (T Tg) (φ g)

GoodJ : (σ : type) → Maj σ → 𝓤₀ ̇
GoodJ σ φ = Σ T ꞉ 𝕋 σ , LJ σ T × ((w : 𝓑) → BndJ σ w T φ)

\end{code}

Ground extraction, the base combinators, and application — as in
`MultHereditaryFT` (`LJ (ι ⇒ ι)` is again definitionally
`GoodT (ι ⇒ ι) × AffBounded`).

\begin{code}

GoodJ-ι-to-<ε₀ : (a : 𝓑) → GoodJ ι a → a < ε₀
GoodJ-ι-to-<ε₀ a (T , (Tpres , Tmono) , bnd) =
 ≤-trans (≤-S (bnd Z)) (Tpres Z Z<ε₀)

GoodJ-Zero : GoodJ ι μ-Zero
GoodJ-Zero =
 (λ w → w) , ((λ w w<ε₀ → w<ε₀) , (λ w w′ w≤w′ → w≤w′)) , (λ w → ≤-Z)

GoodJ-Succ : GoodJ (ι ⇒ ι) μ-Succ
GoodJ-Succ =
 (λ Tg → Tg) , ((λ Tg gTg → gTg) , AffBounded-id) , (λ w g Tg gTg gg → gg w)

GoodJ-Ω : GoodJ (ι ⇒ ι) μ-Ω
GoodJ-Ω =
 (λ Tg w → S (Tg w))
 , ((λ Tg (gp , gm) → (λ w w<ε₀ → S-<-ε₀ (Tg w) (gp w w<ε₀))
                    , (λ w w′ w≤w′ → ≤-S (gm w w′ w≤w′)))
   , AffBounded-S)
 , (λ w g Tg gTg gg → ≤-S (gg w))

GoodJ-app : (σ τ : type) (F : Maj (σ ⇒ τ)) (G : Maj σ)
          → GoodJ (σ ⇒ τ) F → GoodJ σ G → GoodJ τ (F G)
GoodJ-app σ τ F G (TF , (mF , _) , bF) (TG , lG , bG) =
 TF TG , mF TG lG , (λ w → bF w G TG lG bG)

\end{code}

`K`. Two case-splitting helpers: the outer partial application is the binary
first projection (jointly affine, `Aff₂-K`, when both types are `ι`), and
the inner one is the constant functional — `AffBounded-const` at `σ = τ = ι`
as before, and now also `Aff₂-insert` at `σ = ι ⇒ ι`, `τ = ι` (a constant
*binary* functional, its `AffBounded` data reused with a dead argument
slot).

\begin{code}

extraJ-K-outer : (σ τ : type) → Extra σ (τ ⇒ σ) (λ Ta Tb → Ta)
extraJ-K-outer ι         ι         = Aff₂-K
extraJ-K-outer ι         (τ₁ ⇒ τ₂) = ⋆
extraJ-K-outer (σ₁ ⇒ σ₂) τ         = ⋆

extraJ-K-inner : (σ τ : type) (Ta : 𝕋 σ) → LJ σ Ta → Extra τ σ (λ Tb → Ta)
extraJ-K-inner ι                    ι          Ta gTa = AffBounded-const Ta gTa
extraJ-K-inner (ι ⇒ ι)              ι          Ta lTa = Aff₂-insert Ta (pr₂ lTa)
extraJ-K-inner (ι ⇒ (σ₁ ⇒ σ₂))      ι          Ta lTa = ⋆
extraJ-K-inner ((σ₁ ⇒ σ₂) ⇒ σ₃)     ι          Ta lTa = ⋆
extraJ-K-inner ι                    (τ₁ ⇒ τ₂)  Ta lTa = ⋆
extraJ-K-inner (ι ⇒ ι)              (τ₁ ⇒ τ₂)  Ta lTa = ⋆
extraJ-K-inner (ι ⇒ (σ₁ ⇒ σ₂))      (τ₁ ⇒ τ₂)  Ta lTa = ⋆
extraJ-K-inner ((σ₁ ⇒ σ₂) ⇒ σ₃)     (τ₁ ⇒ τ₂)  Ta lTa = ⋆

GoodJ-K : {σ τ : type} → GoodJ (σ ⇒ τ ⇒ σ) μ-K
GoodJ-K {σ} {τ} =
 (λ Ta Tb → Ta)
 , ((λ Ta lTa → (λ Tb lTb → lTa) , extraJ-K-inner σ τ Ta lTa)
   , extraJ-K-outer σ τ)
 , (λ w a Ta lTa a-glob b Tb lTb b-glob → a-glob w)

\end{code}

The four `S` families. All share the transformer
`λ Tφ Tγ Ta → (Tφ Ta) (Tγ Ta)` and the same `BndJ` proof (Design F's
`Good-S`, verbatim); they differ only in the `Extra` obligations at the
diagonal. For `Sg` (all-ground) the diagonal obligation is `AffBounded`, paid
by `AffBounded-Sg-diag` from `Aff₂ Tφ` and `AffBounded Tγ` — the case blocked
in every design before `Aff₂`. For the three function-typed families every
obligation reduces to `𝟙`.

\begin{code}

GoodJ-Sg : GoodJ ((ι ⇒ ι ⇒ ι) ⇒ (ι ⇒ ι) ⇒ ι ⇒ ι) μ-S
GoodJ-Sg =
 (λ Tφ Tγ Ta → (Tφ Ta) (Tγ Ta))
 , ((λ Tφ lTφ →
      ((λ Tγ lTγ →
         ((λ Ta gTa → pr₁ (pr₁ lTφ Ta gTa) (Tγ Ta) (pr₁ lTγ Ta gTa))
          , AffBounded-Sg-diag Tφ Tγ (pr₂ lTφ) (pr₂ lTγ)))
       , ⋆))
    , ⋆)
 , bndS
 where
  bndS : (w : 𝓑)
       → BndJ ((ι ⇒ ι ⇒ ι) ⇒ (ι ⇒ ι) ⇒ ι ⇒ ι) w
              (λ Tφ Tγ Ta → (Tφ Ta) (Tγ Ta)) μ-S
  bndS w φ Tφ lTφ φ-glob γ Tγ lTγ γ-glob a Ta lTa a-glob =
   φ-glob w a Ta lTa a-glob (γ a) (Tγ Ta) (pr₁ lTγ Ta lTa)
     (λ w′ → γ-glob w′ a Ta lTa a-glob)

GoodJ-Sh : {ρ₁ ρ₂ σ τ : type}
         → GoodJ (((ρ₁ ⇒ ρ₂) ⇒ σ ⇒ τ) ⇒ ((ρ₁ ⇒ ρ₂) ⇒ σ) ⇒ (ρ₁ ⇒ ρ₂) ⇒ τ) μ-S
GoodJ-Sh {ρ₁} {ρ₂} {σ} {τ} =
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
       → BndJ (((ρ₁ ⇒ ρ₂) ⇒ σ ⇒ τ) ⇒ ((ρ₁ ⇒ ρ₂) ⇒ σ) ⇒ (ρ₁ ⇒ ρ₂) ⇒ τ) w
              (λ Tφ Tγ Ta → (Tφ Ta) (Tγ Ta)) μ-S
  bndS w φ Tφ lTφ φ-glob γ Tγ lTγ γ-glob a Ta lTa a-glob =
   φ-glob w a Ta lTa a-glob (γ a) (Tγ Ta) (pr₁ lTγ Ta lTa)
     (λ w′ → γ-glob w′ a Ta lTa a-glob)

GoodJ-Sfh : {σ ρ₁ ρ₂ τ₂ : type}
          → GoodJ ((ι ⇒ σ ⇒ (ρ₁ ⇒ ρ₂) ⇒ τ₂) ⇒ (ι ⇒ σ) ⇒ ι ⇒ (ρ₁ ⇒ ρ₂) ⇒ τ₂)
                  μ-S
GoodJ-Sfh {σ} {ρ₁} {ρ₂} {τ₂} =
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
       → BndJ ((ι ⇒ σ ⇒ (ρ₁ ⇒ ρ₂) ⇒ τ₂) ⇒ (ι ⇒ σ) ⇒ ι ⇒ (ρ₁ ⇒ ρ₂) ⇒ τ₂) w
              (λ Tφ Tγ Ta → (Tφ Ta) (Tγ Ta)) μ-S
  bndS w φ Tφ lTφ φ-glob γ Tγ lTγ γ-glob a Ta lTa a-glob =
   φ-glob w a Ta lTa a-glob (γ a) (Tγ Ta) (pr₁ lTγ Ta lTa)
     (λ w′ → γ-glob w′ a Ta lTa a-glob)

GoodJ-Sfr : {σ κ₁ κ₂ : type}
          → GoodJ ((ι ⇒ σ ⇒ ι ⇒ κ₁ ⇒ κ₂) ⇒ (ι ⇒ σ) ⇒ ι ⇒ ι ⇒ κ₁ ⇒ κ₂) μ-S
GoodJ-Sfr {σ} {κ₁} {κ₂} =
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
       → BndJ ((ι ⇒ σ ⇒ ι ⇒ κ₁ ⇒ κ₂) ⇒ (ι ⇒ σ) ⇒ ι ⇒ ι ⇒ κ₁ ⇒ κ₂) w
              (λ Tφ Tγ Ta → (Tφ Ta) (Tγ Ta)) μ-S
  bndS w φ Tφ lTφ φ-glob γ Tγ lTγ γ-glob a Ta lTa a-glob =
   φ-glob w a Ta lTa a-glob (γ a) (Tγ Ta) (pr₁ lTγ Ta lTa)
     (λ w′ → γ-glob w′ a Ta lTa a-glob)

\end{code}

The recursor — unconditional, as in `MultHereditaryFT`, with the additional
joint obligation on its two ground arguments paid by `Aff₂-Iter`.

\begin{code}

GoodJ-Iter : GoodJ ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι) μ-Iter
GoodJ-Iter = (λ Tg Ta Tν w → Torbit Tg Ta w ⊕ Tν w) , lI , bnd
 where
  orbitGood : (Tg : 𝕋 (ι ⇒ ι)) → LJ (ι ⇒ ι) Tg → (Ta : 𝕋 ι) → GoodT ι Ta
            → GoodT ι (Torbit Tg Ta)
  orbitGood Tg (gTg , affTg) Ta gTa = orbit-good-aff Tg gTg affTg Ta gTa

  lI : LJ ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι) (λ Tg Ta Tν w → Torbit Tg Ta w ⊕ Tν w)
  lI = (λ Tg lTg →
         ((λ Ta gTa →
            ((λ Tν gTν → GoodT-⊕ (Torbit Tg Ta) Tν (orbitGood Tg lTg Ta gTa) gTν)
             , AffBounded-add (Torbit Tg Ta) (orbitGood Tg lTg Ta gTa)))
          , Aff₂-Iter Tg (pr₂ lTg)))
       , ⋆

  bnd : (w : 𝓑) → BndJ ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι) w
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

The fragment `T₂`, its embedding into `T₁`, and the embedding of `T★`
witnessing `T₂ ⊇ T★` (coherent over the `T₁` semantics).

\begin{code}

data T₂ : type → 𝓤₀ ̇ where
 Ω₂    : T₂ (ι ⇒ ι)
 Zero₂ : T₂ ι
 Succ₂ : T₂ (ι ⇒ ι)
 Iter₂ : T₂ ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι)
 K₂    : {σ τ : type} → T₂ (σ ⇒ τ ⇒ σ)
 Sg₂   : T₂ ((ι ⇒ ι ⇒ ι) ⇒ (ι ⇒ ι) ⇒ ι ⇒ ι)
 Sh₂   : {ρ₁ ρ₂ σ τ : type}
       → T₂ (((ρ₁ ⇒ ρ₂) ⇒ σ ⇒ τ) ⇒ ((ρ₁ ⇒ ρ₂) ⇒ σ) ⇒ (ρ₁ ⇒ ρ₂) ⇒ τ)
 Sfh₂  : {σ ρ₁ ρ₂ τ₂ : type}
       → T₂ ((ι ⇒ σ ⇒ (ρ₁ ⇒ ρ₂) ⇒ τ₂) ⇒ (ι ⇒ σ) ⇒ ι ⇒ (ρ₁ ⇒ ρ₂) ⇒ τ₂)
 Sfr₂  : {σ κ₁ κ₂ : type}
       → T₂ ((ι ⇒ σ ⇒ ι ⇒ κ₁ ⇒ κ₂) ⇒ (ι ⇒ σ) ⇒ ι ⇒ ι ⇒ κ₁ ⇒ κ₂)
 _·₂_  : {σ τ : type} → T₂ (σ ⇒ τ) → T₂ σ → T₂ τ

infixl 6 _·₂_

e : {σ : type} → T₂ σ → T₁ σ
e Ω₂        = Ω₁
e Zero₂     = Zero₁
e Succ₂     = Succ₁
e Iter₂     = Iter₁
e K₂        = K₁
e Sg₂       = S₁
e Sh₂       = S₁
e Sfh₂      = S₁
e Sfr₂      = S₁
e (t ·₂ u)  = e t ·₁ e u

emb★ : {σ : type} → T★ σ → T₂ σ
emb★ Ω★        = Ω₂
emb★ Zero★     = Zero₂
emb★ Succ★     = Succ₂
emb★ Iter★     = Iter₂
emb★ K★        = K₂
emb★ Sg★       = Sg₂
emb★ Sh★       = Sh₂
emb★ (t ·★ u)  = emb★ t ·₂ emb★ u

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

goodμ : {σ : type} (t : T₂ σ) → GoodJ σ (μ (e t))
goodμ Ω₂        = GoodJ-Ω
goodμ Zero₂     = GoodJ-Zero
goodμ Succ₂     = GoodJ-Succ
goodμ Iter₂     = GoodJ-Iter
goodμ (K₂ {σ} {τ}) = GoodJ-K {σ} {τ}
goodμ Sg₂       = GoodJ-Sg
goodμ (Sh₂ {ρ₁} {ρ₂} {σ} {τ}) = GoodJ-Sh {ρ₁} {ρ₂} {σ} {τ}
goodμ (Sfh₂ {σ} {ρ₁} {ρ₂} {τ₂}) = GoodJ-Sfh {σ} {ρ₁} {ρ₂} {τ₂}
goodμ (Sfr₂ {σ} {κ₁} {κ₂}) = GoodJ-Sfr {σ} {κ₁} {κ₂}
goodμ (t ·₂ u)  = GoodJ-app _ _ (μ (e t)) (μ (e u)) (goodμ t) (goodμ u)

μ-<-ε₀ : (t : T₂ ι) → μ (e t) < ε₀
μ-<-ε₀ t = GoodJ-ι-to-<ε₀ (μ (e t)) (goodμ t)

height-<-ε₀ : (t : T₂ ι) → height ⟦ e t ⟧₁ < ε₀
height-<-ε₀ t = ≤-trans (≤-S (height-≤-μ (e t))) (μ-<-ε₀ t)

dialogue-height-<-ε₀ : (t : T₂ ((ι ⇒ ι) ⇒ ι))
                     → height (⟦ e t ⟧₁ generic) < ε₀
dialogue-height-<-ε₀ t = height-<-ε₀ (t ·₂ Ω₂)

\end{code}
