A fundamental theorem from Design F: unconditional `height < ε₀` for a
first-order fragment including the recursor and — for the first time — a
ground-`S` instance with *function-typed result*, the family blocked in every
`Maj`-level design.

`MultHereditaryF` dissolved the structural wall but left the recursor
conditional on transformer-orbit-closure, which is *false* for the full
`GoodT`. `MultHereditaryFAff` built the inner-affine class `AffBounded` on
which it is *true* (`orbit-good-aff`), closed under everything the fragment
builds. Here the two are joined: the Design-F predicate is refined so that
transformers of type `ι ⇒ ι` additionally carry `AffBounded`:

  `LA ι = GoodT ι`,
  `LA (σ ⇒ τ) T = (maps LA to LA) × ExtraA σ τ T`,

where `ExtraA ι ι = AffBounded` and `ExtraA` is trivial at any other type —
defined by matching on the *codomain first*, so that the obligations arising
in `K` and `S` (whose intermediate codomains are manifestly arrows) reduce
even at abstract types. `BndA`/`GoodA` are `MultHereditaryF`'s `Bnd`/`Good`
with `LA` in place of `GoodT`; the structural proofs port verbatim. The
refinement is paid for at exactly four places, each an `MultHereditaryFAff`
lemma: `Succ ↦ AffBounded-id`, `Ω ↦ AffBounded-S`, `K`'s inner constant
`↦ AffBounded-const`, and the recursor's partial application
`↦ AffBounded-add` — with the orbit's `GoodT` discharged by `orbit-good-aff`
from the `AffBounded` carried by the iterated argument. **The recursor is
unconditional in this predicate.**

The fragment `T⁺` has `Ω/Zero/Succ/Iter/K/·` and `S` at two instance
families: `Sh⁺` (shared argument function-typed, as in `MultHereditaryT`'s
`T★`) and — **new, beyond `T★`** — `Sf⁺`: shared argument `ι` and
*function-typed result* `τ`, with the middle type `σ` arbitrary. `Sf⁺` was in
the blocked family ("ground `S` with a function-typed `σ` or `τ`"): here its
`ExtraA` obligations are all trivial by the codomain-first reduction, and the
Design-F transformer mechanism does the rest. Honest scope: `T⁺` does *not*
include `T★`'s all-ground instance `Sg★` (`ρ = σ = τ = ι`) — its diagonal
needs a *joint* binary affine bound (`AffBounded` in two arguments at once),
which this simple refinement does not carry; nor ground-`S` with
function-typed *middle* `σ` and ground result, where the affine data of the
diagonal would have to depend on the function argument's data (Howard's
transformer tower). Unifying `T★` and `T⁺` needs the joint (`n`-ary)
refinement — the next step, not taken here. The conjecture for full System T
remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryFT
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
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

\end{code}

The refined predicate. `ExtraA` matches on the codomain first: at an arrow
codomain there is no obligation (this clause fires without inspecting the
domain, which is what lets `K` and `S` typecheck at abstract types); at
codomain `ι` the domain decides — `AffBounded` when it is `ι`, nothing when
it is an arrow.

\begin{code}

ExtraA : (σ τ : type) → 𝕋 (σ ⇒ τ) → 𝓤₀ ̇
ExtraA σ         (τ₁ ⇒ τ₂) T = 𝟙
ExtraA ι         ι         T = AffBounded T
ExtraA (σ₁ ⇒ σ₂) ι         T = 𝟙

LA : (σ : type) → 𝕋 σ → 𝓤₀ ̇
LA ι       T = GoodT ι T
LA (σ ⇒ τ) T = ((Tg : 𝕋 σ) → LA σ Tg → LA τ (T Tg)) × ExtraA σ τ T

BndA : (σ : type) → 𝓑 → 𝕋 σ → Maj σ → 𝓤₀ ̇
BndA ι       w T a = a ≤ T w
BndA (σ ⇒ τ) w T φ = (g : Maj σ) (Tg : 𝕋 σ) → LA σ Tg
                   → ((w′ : 𝓑) → BndA σ w′ Tg g) → BndA τ w (T Tg) (φ g)

GoodA : (σ : type) → Maj σ → 𝓤₀ ̇
GoodA σ φ = Σ T ꞉ 𝕋 σ , LA σ T × ((w : 𝓑) → BndA σ w T φ)

\end{code}

Note `LA (ι ⇒ ι) T` is *definitionally* `GoodT (ι ⇒ ι) T × AffBounded T`, so
the `MultHereditaryFAff` lemmas plug in with no conversion.

Ground extraction and the base combinators — as in `MultHereditaryF`, plus
the `ExtraA` component from the affine class.

\begin{code}

GoodA-ι-to-<ε₀ : (a : 𝓑) → GoodA ι a → a < ε₀
GoodA-ι-to-<ε₀ a (T , (Tpres , Tmono) , bnd) =
 ≤-trans (≤-S (bnd Z)) (Tpres Z Z<ε₀)

GoodA-Zero : GoodA ι μ-Zero
GoodA-Zero =
 (λ w → w) , ((λ w w<ε₀ → w<ε₀) , (λ w w′ w≤w′ → w≤w′)) , (λ w → ≤-Z)

GoodA-Succ : GoodA (ι ⇒ ι) μ-Succ
GoodA-Succ =
 (λ Tg → Tg) , ((λ Tg gTg → gTg) , AffBounded-id) , (λ w g Tg gTg gg → gg w)

GoodA-Ω : GoodA (ι ⇒ ι) μ-Ω
GoodA-Ω =
 (λ Tg w → S (Tg w))
 , ((λ Tg (gp , gm) → (λ w w<ε₀ → S-<-ε₀ (Tg w) (gp w w<ε₀))
                    , (λ w w′ w≤w′ → ≤-S (gm w w′ w≤w′)))
   , AffBounded-S)
 , (λ w g Tg gTg gg → ≤-S (gg w))

\end{code}

Application: drop the function's `ExtraA`, apply its mapping component.

\begin{code}

GoodA-app : (σ τ : type) (F : Maj (σ ⇒ τ)) (G : Maj σ)
          → GoodA (σ ⇒ τ) F → GoodA σ G → GoodA τ (F G)
GoodA-app σ τ F G (TF , (mF , _) , bF) (TG , lG , bG) =
 TF TG , mF TG lG , (λ w → bF w G TG lG bG)

\end{code}

`K`. The outer obligation `ExtraA σ (τ ⇒ σ)` reduces to `𝟙` (arrow codomain);
the inner one `ExtraA τ σ` is decided by cases — when both are `ι` the
partial application `λ Tb → Ta` is the constant functional, which is
inner-affine by `AffBounded-const` (this is exactly the "K yields a constant"
subtlety, landing where the class was built for it).

\begin{code}

extraA-K : (σ τ : type) (Ta : 𝕋 σ) → LA σ Ta → ExtraA τ σ (λ Tb → Ta)
extraA-K ι         ι          Ta gTa = AffBounded-const Ta gTa
extraA-K ι         (τ₁ ⇒ τ₂)  Ta lTa = ⋆
extraA-K (σ₁ ⇒ σ₂) τ          Ta lTa = ⋆

GoodA-K : {σ τ : type} → GoodA (σ ⇒ τ ⇒ σ) μ-K
GoodA-K {σ} {τ} =
 (λ Ta Tb → Ta)
 , ((λ Ta lTa → (λ Tb lTb → lTa) , extraA-K σ τ Ta lTa) , ⋆)
 , (λ w a Ta lTa a-glob b Tb lTb b-glob → a-glob w)

\end{code}

The two `S` families. The first two levels' obligations reduce to `𝟙` in both
(arrow codomains). At the diagonal `λ Ta → (Tφ Ta) (Tγ Ta)`:

* `Sh` (shared argument function-typed): `ExtraA (ρ₁ ⇒ ρ₂) τ` is `𝟙` by
  cases on `τ`;
* `Sf` (shared argument `ι`, function-typed result): `ExtraA ι (τ₁ ⇒ τ₂)`
  reduces to `𝟙` outright — *no affine content at all*, which is why this
  previously-blocked family is free here.

The mapping and bound components are `MultHereditaryF.Good-S` verbatim.

\begin{code}

extraA-diag-h : (ρ₁ ρ₂ τ : type) (T : 𝕋 ((ρ₁ ⇒ ρ₂) ⇒ τ))
              → ExtraA (ρ₁ ⇒ ρ₂) τ T
extraA-diag-h ρ₁ ρ₂ ι         T = ⋆
extraA-diag-h ρ₁ ρ₂ (τ₁ ⇒ τ₂) T = ⋆

GoodA-Sh : {ρ₁ ρ₂ σ τ : type}
         → GoodA (((ρ₁ ⇒ ρ₂) ⇒ σ ⇒ τ) ⇒ ((ρ₁ ⇒ ρ₂) ⇒ σ) ⇒ (ρ₁ ⇒ ρ₂) ⇒ τ) μ-S
GoodA-Sh {ρ₁} {ρ₂} {σ} {τ} =
 (λ Tφ Tγ Ta → (Tφ Ta) (Tγ Ta))
 , ((λ Tφ lTφ →
      ((λ Tγ lTγ →
         ((λ Ta lTa → pr₁ (pr₁ lTφ Ta lTa) (Tγ Ta) (pr₁ lTγ Ta lTa))
          , extraA-diag-h ρ₁ ρ₂ τ (λ Ta → (Tφ Ta) (Tγ Ta))))
       , ⋆))
    , ⋆)
 , bndS
 where
  bndS : (w : 𝓑)
       → BndA (((ρ₁ ⇒ ρ₂) ⇒ σ ⇒ τ) ⇒ ((ρ₁ ⇒ ρ₂) ⇒ σ) ⇒ (ρ₁ ⇒ ρ₂) ⇒ τ) w
              (λ Tφ Tγ Ta → (Tφ Ta) (Tγ Ta)) μ-S
  bndS w φ Tφ lTφ φ-glob γ Tγ lTγ γ-glob a Ta lTa a-glob =
   φ-glob w a Ta lTa a-glob (γ a) (Tγ Ta) (pr₁ lTγ Ta lTa)
     (λ w′ → γ-glob w′ a Ta lTa a-glob)

GoodA-Sf : {σ τ₁ τ₂ : type}
         → GoodA ((ι ⇒ σ ⇒ τ₁ ⇒ τ₂) ⇒ (ι ⇒ σ) ⇒ ι ⇒ τ₁ ⇒ τ₂) μ-S
GoodA-Sf {σ} {τ₁} {τ₂} =
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
       → BndA ((ι ⇒ σ ⇒ τ₁ ⇒ τ₂) ⇒ (ι ⇒ σ) ⇒ ι ⇒ τ₁ ⇒ τ₂) w
              (λ Tφ Tγ Ta → (Tφ Ta) (Tγ Ta)) μ-S
  bndS w φ Tφ lTφ φ-glob γ Tγ lTγ γ-glob a Ta lTa a-glob =
   φ-glob w a Ta lTa a-glob (γ a) (Tγ Ta) (pr₁ lTγ Ta lTa)
     (λ w′ → γ-glob w′ a Ta lTa a-glob)

\end{code}

The recursor — **unconditional**. The iterated argument's `LA (ι ⇒ ι)` is
`GoodT × AffBounded`, so `orbit-good-aff` discharges the orbit transformer's
`GoodT`, and the partial application `λ Tν w → Torbit Tg Ta w ⊕ Tν w` is
inner-affine by `AffBounded-add`. The `BndA` component is
`MultHereditaryF.Good-Iter`'s unconditional `orbit-pt` induction, verbatim.

\begin{code}

GoodA-Iter : GoodA ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι) μ-Iter
GoodA-Iter = (λ Tg Ta Tν w → Torbit Tg Ta w ⊕ Tν w) , lI , bnd
 where
  orbitGood : (Tg : 𝕋 (ι ⇒ ι)) → LA (ι ⇒ ι) Tg → (Ta : 𝕋 ι) → GoodT ι Ta
            → GoodT ι (Torbit Tg Ta)
  orbitGood Tg (gTg , affTg) Ta gTa = orbit-good-aff Tg gTg affTg Ta gTa

  lI : LA ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι) (λ Tg Ta Tν w → Torbit Tg Ta w ⊕ Tν w)
  lI = (λ Tg lTg →
         ((λ Ta gTa →
            ((λ Tν gTν → GoodT-⊕ (Torbit Tg Ta) Tν (orbitGood Tg lTg Ta gTa) gTν)
             , AffBounded-add (Torbit Tg Ta) (orbitGood Tg lTg Ta gTa)))
          , ⋆))
       , ⋆

  bnd : (w : 𝓑) → BndA ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι) w
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

The fragment `T⁺` and its embedding into `T₁` (both `S` constructors map to
`S₁`, so `Majorant`'s semantics and majorant apply unchanged).

\begin{code}

data T⁺ : type → 𝓤₀ ̇ where
 Ω⁺    : T⁺ (ι ⇒ ι)
 Zero⁺ : T⁺ ι
 Succ⁺ : T⁺ (ι ⇒ ι)
 Iter⁺ : T⁺ ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι)
 K⁺    : {σ τ : type} → T⁺ (σ ⇒ τ ⇒ σ)
 Sh⁺   : {ρ₁ ρ₂ σ τ : type}
       → T⁺ (((ρ₁ ⇒ ρ₂) ⇒ σ ⇒ τ) ⇒ ((ρ₁ ⇒ ρ₂) ⇒ σ) ⇒ (ρ₁ ⇒ ρ₂) ⇒ τ)
 Sf⁺   : {σ τ₁ τ₂ : type}
       → T⁺ ((ι ⇒ σ ⇒ τ₁ ⇒ τ₂) ⇒ (ι ⇒ σ) ⇒ ι ⇒ τ₁ ⇒ τ₂)
 _·⁺_  : {σ τ : type} → T⁺ (σ ⇒ τ) → T⁺ σ → T⁺ τ

infixl 6 _·⁺_

e : {σ : type} → T⁺ σ → T₁ σ
e Ω⁺        = Ω₁
e Zero⁺     = Zero₁
e Succ⁺     = Succ₁
e Iter⁺     = Iter₁
e K⁺        = K₁
e Sh⁺       = S₁
e Sf⁺       = S₁
e (t ·⁺ u)  = e t ·₁ e u

\end{code}

The fundamental theorem and its payoffs: the majorant of any ground `T⁺` term
is `< ε₀`, hence — by `Majorant.height-≤-μ` — so is its height, and in
particular the dialogue-tree height of any `t : T⁺ ((ι ⇒ ι) ⇒ ι)`,
unconditionally.

\begin{code}

goodμ : {σ : type} (t : T⁺ σ) → GoodA σ (μ (e t))
goodμ Ω⁺        = GoodA-Ω
goodμ Zero⁺     = GoodA-Zero
goodμ Succ⁺     = GoodA-Succ
goodμ Iter⁺     = GoodA-Iter
goodμ (K⁺ {σ} {τ}) = GoodA-K {σ} {τ}
goodμ (Sh⁺ {ρ₁} {ρ₂} {σ} {τ}) = GoodA-Sh {ρ₁} {ρ₂} {σ} {τ}
goodμ (Sf⁺ {σ} {τ₁} {τ₂}) = GoodA-Sf {σ} {τ₁} {τ₂}
goodμ (t ·⁺ u)  = GoodA-app _ _ (μ (e t)) (μ (e u)) (goodμ t) (goodμ u)

μ-<-ε₀ : (t : T⁺ ι) → μ (e t) < ε₀
μ-<-ε₀ t = GoodA-ι-to-<ε₀ (μ (e t)) (goodμ t)

height-<-ε₀ : (t : T⁺ ι) → height ⟦ e t ⟧₁ < ε₀
height-<-ε₀ t = ≤-trans (≤-S (height-≤-μ (e t))) (μ-<-ε₀ t)

dialogue-height-<-ε₀ : (t : T⁺ ((ι ⇒ ι) ⇒ ι))
                     → height (⟦ e t ⟧₁ generic) < ε₀
dialogue-height-<-ε₀ t = height-<-ε₀ (t ·⁺ Ω⁺)

\end{code}
