The affine transformer class: the closure of linear, constant and additive
functionals under composition and the recursor orbit — the complete `ι ⇒ ι`
transformer algebra of the first-order fragment.

`MultHereditaryFLin` discharged the recursor's orbit-closure hypothesis
separately on the three basic shapes a first-order term generates — linear
(`orbit-good-lin`), constant (`orbit-good-const`) and left-additive
(`orbit-good-add`) — but those shapes are not closed under composition: the
composite of a linear and an additive functional has the additive part `D`
*inside* the multiplier, `T ↦ (D w ⊕ (T w ⊕ c)) ⊗ M`, and it cannot be moved
out (`⊕` is not commutative below `ε₀`; `⊗` does not distribute from the
left). The resolution is to take that composite shape as the *definition* of
the class:

  `AffBounded Tg = Σ D c M , GoodT D × c < ε₀ × ValidMult M
                           × (∀ T w → Tg T w ≤ (D w ⊕ (T w ⊕ c)) ⊗ M)`

— the **inner-affine** functionals, with the additive summand `D` placed
inside the multiplied zone from the start. Then nothing ever needs to escape
a multiplier, and the class is closed under everything the fragment builds:

* the three basic shapes embed (`AffBounded-lin/const/add`, and `id`, `S`);
* **composition** (`AffBounded-∘`): the inner zones merge — the outer `D_f`
  and constant `c_f` are absorbed into the inner zone enlarged to
  `Y′ = ((D_f ⊕ D_g) ⊕ (T ⊕ (c_g ⊕ c_f))) ⊗ M_g` by a triple absorption
  `Y′ ⊕ (Y′ ⊕ Y′) ≤ Y′ ⊗ ω`, giving multiplier `M_g ⊗ (ω ⊗ M_f)` (no
  `affine-fold`, and no `crux` — absorption by `⊗ ω` replaces it);
* **the recursor orbit** (`AffBounded-orbit`): iterating an inner-affine
  functional is dominated by iterating the `MDom` body `b ↦ (b ⊕ c) ⊗ (ω ⊗ M)`
  from the start `D w ⊕ T w`, by the invariant "`D w` stays below the
  majorant" — so `MultAffine.mbody-orbit-≤` bounds the orbit at multiplier
  `ω^((ω ⊗ M) ⊗ ω)`, again `ValidMult`, again inner-affine with the *same*
  `D` and `c`;
* hence **`orbit-good-aff`**: the orbit transformer of a `GoodT`,
  inner-affine functional is `GoodT` — `MultHereditaryF.Good-Iter`'s
  hypothesis holds on the whole class, subsuming the three per-shape
  discharges of `MultHereditaryFLin`.

So the transformer-class arithmetic for the first-order fragment is complete:
one class, closed under identity, successor, composition and orbit, containing
every combinator shape, with the orbit-closure discharged uniformly. What
remains for the fragment's fundamental theorem is not arithmetic but
plumbing: a `Good`-style logical relation over a concrete first-order syntax
whose `ι ⇒ ι` clause carries `AffBounded`, and the height connection via
`Majorant`. The conjecture for full System T remains open (the genuinely
super-linear transformers, e.g. squaring, lie outside this class —
`MultSquareOrbit` shows their orbits are still `< ε₀`, but no closed class
containing them is known).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryFAff
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left ; ⊕-assoc)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ω^_ ; ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right ;
        ⊕-increasing-right ; ⊕-<-ε₀ ; ω^-<-ε₀ ; tower-<-ε₀)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊗-assoc ; ⊕-increasing-left)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (⊗-<-ε₀)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (x-≤-x⊗ ; Z<ε₀)
open import Claude.BrouwerOrdinals.MultAffine fe
 using (mbody-orbit-≤ ; ω-pos)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; ω-valid ; validMult-⊗ ; validMult-orbit)
open import Claude.DialogueTreeHeight.MultHereditaryF fe
 using (𝕋 ; GoodT ; Torbit ; GoodT-iter ; GoodT-⊕)
open import Claude.DialogueTreeHeight.MultHereditaryFLin fe
 using (LinBounded ; LinBounded-id ; LinBounded-S)

\end{code}

Absorption by `⊗ ω`: a sum of two or three copies of `x` is below `x ⊗ ω`,
since `x ⊕ x ≤ x ⊗ ι[ 2 ]` and `(x ⊕ x) ⊕ x ≤ x ⊗ ι[ 3 ]` (the `Z ⊕ x` in
the numeral products absorbs `x` on the left). This replaces `crux`: instead
of cancelling a constant against a copy of the zone, we pay one factor of `ω`
in the multiplier and absorb *everything* that is below the zone.

\begin{code}

⊕-dup-≤-⊗ω : (x : 𝓑) → (x ⊕ x) ≤ (x ⊗ ω)
⊕-dup-≤-⊗ω x =
 ≤-trans (⊕-mono-left (⊕-increasing-left Z x) x)
         (⊗-mono-right x (≤-L-upper-bound ι[_] 2))

⊕-trip-≤-⊗ω : (x : 𝓑) → (x ⊕ (x ⊕ x)) ≤ (x ⊗ ω)
⊕-trip-≤-⊗ω x =
 transport (λ z → z ≤ (x ⊗ ω)) (⊕-assoc x x x)
  (≤-trans (⊕-mono-left (⊕-mono-left (⊕-increasing-left Z x) x) x)
           (⊗-mono-right x (≤-L-upper-bound ι[_] 3)))

\end{code}

The class. A functional is inner-affine if it is bounded by a single
multiplied zone containing an additive summand `D` (a `GoodT` transformer of
the weight), the argument, and a constant `c < ε₀`.

\begin{code}

AffBounded : 𝕋 (ι ⇒ ι) → 𝓤₀ ̇
AffBounded Tg =
 Σ D ꞉ (𝓑 → 𝓑) , Σ c ꞉ 𝓑 , Σ M ꞉ 𝓑 ,
    GoodT ι D × (c < ε₀) × ValidMult M
  × ((T : 𝓑 → 𝓑) (w : 𝓑) → Tg T w ≤ ((D w ⊕ (T w ⊕ c)) ⊗ M))

\end{code}

The three basic shapes embed: linear (`D = Z`), constant (`D` the constant
itself, which ignores the argument slot), and left-additive (`D` the added
summand, `c = Z`, `M = ω`). Identity and successor come via the linear
embedding.

\begin{code}

AffBounded-lin : (Tg : 𝕋 (ι ⇒ ι)) → LinBounded Tg → AffBounded Tg
AffBounded-lin Tg (c , M , c<ε₀ , vM , lin) =
 (λ _ → Z) , c , M
 , ((λ w _ → Z<ε₀) , (λ w w′ _ → ≤-Z))
 , c<ε₀ , vM , bound
 where
  bound : (T : 𝓑 → 𝓑) (w : 𝓑) → Tg T w ≤ ((Z ⊕ (T w ⊕ c)) ⊗ M)
  bound T w = ≤-trans (lin T w)
                      (⊗-mono-left (⊕-increasing-left Z (T w ⊕ c)) M)

AffBounded-const : (Ta : 𝓑 → 𝓑) → GoodT ι Ta → AffBounded (λ _ → Ta)
AffBounded-const Ta gTa = Ta , Z , ω , gTa , Z<ε₀ , ω-valid , bound
 where
  bound : (T : 𝓑 → 𝓑) (w : 𝓑) → Ta w ≤ ((Ta w ⊕ (T w ⊕ Z)) ⊗ ω)
  bound T w = ≤-trans (⊕-increasing-right (Ta w) (T w))
                      (x-≤-x⊗ (Ta w ⊕ T w) ω ω-pos)

AffBounded-add : (C : 𝓑 → 𝓑) → GoodT ι C → AffBounded (λ Tν w → C w ⊕ Tν w)
AffBounded-add C gC = C , Z , ω , gC , Z<ε₀ , ω-valid , bound
 where
  bound : (T : 𝓑 → 𝓑) (w : 𝓑) → (C w ⊕ T w) ≤ ((C w ⊕ (T w ⊕ Z)) ⊗ ω)
  bound T w = x-≤-x⊗ (C w ⊕ T w) ω ω-pos

AffBounded-id : AffBounded (λ T → T)
AffBounded-id = AffBounded-lin (λ T → T) LinBounded-id

AffBounded-S : AffBounded (λ T w → S (T w))
AffBounded-S = AffBounded-lin (λ T w → S (T w)) LinBounded-S

\end{code}

Composition closure — the arithmetic that forced the class to be inner-affine.
Post-composing the inner bound of `Tg` into the bound of `Tf` gives
`Tf (Tg T) w ≤ (D_f w ⊕ (Y ⊕ c_f)) ⊗ M_f` where `Y` is `Tg`'s zone. Enlarge
`Y` to `Y′ = ((D_f w ⊕ D_g w) ⊕ (T w ⊕ (c_g ⊕ c_f))) ⊗ M_g`: then `D_f w`,
`Y` and `c_f` all sit below `Y′`, the triple absorption packs them into
`Y′ ⊗ ω`, and re-associating `⊗` lands in inner-affine form at summand
`D_f ⊕ D_g`, constant `c_g ⊕ c_f` and multiplier `M_g ⊗ (ω ⊗ M_f)`.

\begin{code}

AffBounded-∘ : (Tf Tg : 𝕋 (ι ⇒ ι)) → AffBounded Tf → AffBounded Tg
             → AffBounded (λ T → Tf (Tg T))
AffBounded-∘ Tf Tg (Df , cf , Mf , gDf , cf<ε₀ , vMf , afff)
                   (Dg , cg , Mg , gDg , cg<ε₀ , vMg@(Mg+ , _ , _) , affg) =
 (λ w → Df w ⊕ Dg w) , (cg ⊕ cf) , (Mg ⊗ (ω ⊗ Mf))
 , GoodT-⊕ Df Dg gDf gDg
 , ⊕-<-ε₀ cg cf cg<ε₀ cf<ε₀
 , validMult-⊗ vMg (validMult-⊗ ω-valid vMf)
 , bound
 where
  bound : (T : 𝓑 → 𝓑) (w : 𝓑)
        → Tf (Tg T) w
          ≤ (((Df w ⊕ Dg w) ⊕ (T w ⊕ (cg ⊕ cf))) ⊗ (Mg ⊗ (ω ⊗ Mf)))
  bound T w =
   transport (λ z → Tf (Tg T) w ≤ z) (⊗-assoc base Mg (ω ⊗ Mf))
    (transport (λ z → Tf (Tg T) w ≤ z) (⊗-assoc Y′ ω Mf) chain)
   where
    base : 𝓑
    base = (Df w ⊕ Dg w) ⊕ (T w ⊕ (cg ⊕ cf))

    Y′ : 𝓑
    Y′ = base ⊗ Mg

    base≤Y′ : base ≤ Y′
    base≤Y′ = x-≤-x⊗ base Mg Mg+

    zone-mono : (Dg w ⊕ (T w ⊕ cg)) ≤ base
    zone-mono =
     ≤-trans (⊕-mono-left (⊕-increasing-left (Df w) (Dg w)) (T w ⊕ cg))
             (⊕-mono-right (Df w ⊕ Dg w)
                           (⊕-mono-right (T w) (⊕-increasing-right cg cf)))

    TgT≤Y′ : Tg T w ≤ Y′
    TgT≤Y′ = ≤-trans (affg T w) (⊗-mono-left zone-mono Mg)

    Df≤Y′ : Df w ≤ Y′
    Df≤Y′ = ≤-trans (⊕-increasing-right (Df w) (Dg w))
             (≤-trans (⊕-increasing-right (Df w ⊕ Dg w) (T w ⊕ (cg ⊕ cf)))
                      base≤Y′)

    cf≤Y′ : cf ≤ Y′
    cf≤Y′ = ≤-trans (⊕-increasing-left cg cf)
             (≤-trans (⊕-increasing-left (T w) (cg ⊕ cf))
              (≤-trans (⊕-increasing-left (Df w ⊕ Dg w) (T w ⊕ (cg ⊕ cf)))
                       base≤Y′))

    packed : (Df w ⊕ (Tg T w ⊕ cf)) ≤ (Y′ ⊕ (Y′ ⊕ Y′))
    packed = ≤-trans (⊕-mono-left Df≤Y′ (Tg T w ⊕ cf))
              (⊕-mono-right Y′ (≤-trans (⊕-mono-left TgT≤Y′ cf)
                                        (⊕-mono-right Y′ cf≤Y′)))

    chain : Tf (Tg T) w ≤ ((Y′ ⊗ ω) ⊗ Mf)
    chain = ≤-trans (afff (Tg T) w)
             (⊗-mono-left (≤-trans packed (⊕-trip-≤-⊗ω Y′)) Mf)

\end{code}

The orbit bound. Iterating an inner-affine `Tg` from `T` is dominated,
pointwise in the weight, by iterating the `MDom` body `b ↦ (b ⊕ c) ⊗ (ω ⊗ M)`
from the start `D w ⊕ T w`. The invariant carried through the induction is
that the majorant also stays above `D w` — so at each step the summand
`D w` inside `Tg`'s zone can be replaced by the majorant itself, and the
doubled zone is absorbed by the extra `ω` in the multiplier. Then
`MultAffine.mbody-orbit-≤` bounds the orbit supremum. No `GoodT` hypothesis
on `Tg` or `T` is needed for the bound itself.

\begin{code}

aff-orbit-≤ : (Tg : 𝕋 (ι ⇒ ι)) (D : 𝓑 → 𝓑) (c M : 𝓑) → ValidMult M
            → ((T : 𝓑 → 𝓑) (w : 𝓑) → Tg T w ≤ ((D w ⊕ (T w ⊕ c)) ⊗ M))
            → (T : 𝓑 → 𝓑) (w : 𝓑)
            → Torbit Tg T w ≤ (((D w ⊕ T w) ⊕ c) ⊗ ω^ ((ω ⊗ M) ⊗ ω))
aff-orbit-≤ Tg D c M vM aff T w =
 ≤-trans (≤-L-mono (λ k → pr₁ (dom k)))
         (mbody-orbit-≤ (ω ⊗ M) M′+ M′dbl c (D w ⊕ T w))
 where
  vM′ : ValidMult (ω ⊗ M)
  vM′ = validMult-⊗ ω-valid vM

  M′+ : S Z ≤ (ω ⊗ M)
  M′+ = pr₁ vM′

  M′dbl : (ι[ 2 ] ⊗ (ω ⊗ M)) ≤ (ω ⊗ M)
  M′dbl = pr₁ (pr₂ vM′)

  mbody′ : 𝓑 → 𝓑
  mbody′ b = (b ⊕ c) ⊗ (ω ⊗ M)

  y : ℕ → 𝓑
  y k = iter mbody′ (D w ⊕ T w) k

  dom : (k : ℕ) → (iter Tg T k w ≤ y k) × (D w ≤ y k)
  dom zero     = ⊕-increasing-left (D w) (T w) , ⊕-increasing-right (D w) (T w)
  dom (succ k) = step , Dstep
   where
    ih₁ : iter Tg T k w ≤ y k
    ih₁ = pr₁ (dom k)

    ih₂ : D w ≤ y k
    ih₂ = pr₂ (dom k)

    zone≤ : (D w ⊕ (iter Tg T k w ⊕ c)) ≤ (y k ⊕ (y k ⊕ c))
    zone≤ = ≤-trans (⊕-mono-left ih₂ (iter Tg T k w ⊕ c))
                    (⊕-mono-right (y k) (⊕-mono-left ih₁ c))

    absorb : (y k ⊕ (y k ⊕ c)) ≤ ((y k ⊕ c) ⊗ ω)
    absorb = ≤-trans (⊕-mono-left (⊕-increasing-right (y k) c) (y k ⊕ c))
                     (⊕-dup-≤-⊗ω (y k ⊕ c))

    step : iter Tg T (succ k) w ≤ y (succ k)
    step = transport (λ z → iter Tg T (succ k) w ≤ z)
                     (⊗-assoc (y k ⊕ c) ω M)
                     (≤-trans (aff (iter Tg T k) w)
                              (⊗-mono-left (≤-trans zone≤ absorb) M))

    Dstep : D w ≤ y (succ k)
    Dstep = ≤-trans ih₂ (≤-trans (⊕-increasing-right (y k) c)
                                 (x-≤-x⊗ (y k ⊕ c) (ω ⊗ M) M′+))

\end{code}

The two payoffs. First, `orbit-good-aff`: the orbit transformer of a `GoodT`,
inner-affine functional is `GoodT` — the recursor's orbit-closure hypothesis
holds on the whole class (subsuming `orbit-good-lin/const/add`, which are the
images of the three embeddings).

\begin{code}

orbit-good-aff : (Tg : 𝕋 (ι ⇒ ι)) → GoodT (ι ⇒ ι) Tg → AffBounded Tg
               → (Ta : 𝓑 → 𝓑) → GoodT ι Ta → GoodT ι (Torbit Tg Ta)
orbit-good-aff Tg gTg (D , c , M , (Dpres , Dmono) , c<ε₀ , vM , aff)
               Ta gTa@(Tapres , Tamono) = pres , mono
 where
  pres : (w : 𝓑) → w < ε₀ → Torbit Tg Ta w < ε₀
  pres w w<ε₀ = ≤-trans (≤-S (aff-orbit-≤ Tg D c M vM aff Ta w)) bound<ε₀
   where
    M′<ε₀ : (ω ⊗ M) < ε₀
    M′<ε₀ = pr₂ (pr₂ (validMult-⊗ ω-valid vM))

    bound<ε₀ : (((D w ⊕ Ta w) ⊕ c) ⊗ ω^ ((ω ⊗ M) ⊗ ω)) < ε₀
    bound<ε₀ =
     ⊗-<-ε₀ ((D w ⊕ Ta w) ⊕ c) (ω^ ((ω ⊗ M) ⊗ ω))
            (⊕-<-ε₀ (D w ⊕ Ta w) c
                    (⊕-<-ε₀ (D w) (Ta w) (Dpres w w<ε₀) (Tapres w w<ε₀))
                    c<ε₀)
            (ω^-<-ε₀ ((ω ⊗ M) ⊗ ω) (⊗-<-ε₀ (ω ⊗ M) ω M′<ε₀ (tower-<-ε₀ 0)))

  mono : (w w′ : 𝓑) → w ≤ w′ → Torbit Tg Ta w ≤ Torbit Tg Ta w′
  mono w w′ w≤w′ =
   ≤-L-mono (λ k → pr₂ (GoodT-iter Tg Ta gTg gTa k) w w′ w≤w′)

\end{code}

Second, the class is closed under the orbit itself: the orbit of an
inner-affine functional is inner-affine with the *same* summand `D` and
constant `c`, at the raised multiplier `ω^((ω ⊗ M) ⊗ ω)` (still `ValidMult`,
by `validMult-orbit`). So arbitrary finite nesting of first-order recursors
stays in the class, one `ω`-exponentiation per nesting level.

\begin{code}

AffBounded-orbit : (Tg : 𝕋 (ι ⇒ ι)) → AffBounded Tg
                 → AffBounded (λ Ta → Torbit Tg Ta)
AffBounded-orbit Tg (D , c , M , gD , c<ε₀ , vM , aff) =
 D , c , ω^ ((ω ⊗ M) ⊗ ω) , gD , c<ε₀
 , validMult-orbit (validMult-⊗ ω-valid vM)
 , bound
 where
  bound : (T : 𝓑 → 𝓑) (w : 𝓑)
        → Torbit Tg T w ≤ ((D w ⊕ (T w ⊕ c)) ⊗ ω^ ((ω ⊗ M) ⊗ ω))
  bound T w =
   transport (λ z → Torbit Tg T w ≤ (z ⊗ ω^ ((ω ⊗ M) ⊗ ω)))
             (⊕-assoc (D w) (T w) c)
             (aff-orbit-≤ Tg D c M vM aff T w)

\end{code}
