Discharging `MultHereditaryF.Good-Iter`'s orbit hypothesis for linearly-bounded
functionals — the recursor's linear case, closed via the `MDom` orbit engine.

`MultHereditaryF.Good-Iter` reduces the recursor to a single hypothesis
`orbit-good : GoodT (Torbit Tg Ta)`, which is *false* for the full `GoodT` (the
`ω`-exponentiation functional is `GoodT` yet its orbit reaches `ε₀`). The residual
is therefore to discharge it on a sub-exponential subclass. This module discharges
it on the **linearly-bounded** functionals: those `Tg` whose output is
`Tg T w ≤ (T w ⊕ c) ⊗ M` for a fixed constant `c < ε₀` and `ValidMult` multiplier
`M` — exactly the shape a recursor with a *linear* iterated body produces
(identity, successor, oracle-relabel, and their composites).

For such `Tg`, iterating `Tg` on `Ta` is dominated pointwise by iterating the
`MDom` body `b ↦ (b ⊕ c) ⊗ M` on `Ta w`, so `MultAffine.mbody-orbit-≤` bounds the
orbit by `(Ta w ⊕ c) ⊗ ω^(M ⊗ ω) < ε₀`. So `orbit-good` holds here — the recursor
closes for linear bodies with no hypothesis, and the surviving gap is only the
genuinely super-linear transformers (squaring etc., `MultSquareOrbit`), which the
same pattern reaches with the `ω`-power orbit bound in place of `mbody-orbit-≤`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryFLin
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ω^_ ; ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right ;
        ⊕-increasing-right ; ⊕-<-ε₀ ; ω^-<-ε₀ ; tower-<-ε₀)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊗-assoc ; ⊕-increasing-left)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (⊗-<-ε₀)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (x-≤-x⊗ ; Z<ε₀ ; ι<ε₀)
open import Claude.BrouwerOrdinals.MultAffine fe
 using (mbody-orbit-≤ ; crux ; ω-pos)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; ω-valid ; validMult-⊗ ; validMult-orbit)
open import Claude.DialogueTreeHeight.Nested fe using (orbit-left-sup-≤)
open import Claude.DialogueTreeHeight.MultHereditaryF fe
 using (𝕋 ; GoodT ; Torbit ; GoodT-iter ; GoodT-⊕)

\end{code}

A functional is linearly bounded if it post-composes with an `MDom` step.

\begin{code}

LinBounded : 𝕋 (ι ⇒ ι) → 𝓤₀ ̇
LinBounded Tg =
 Σ c ꞉ 𝓑 , Σ M ꞉ 𝓑 , (c < ε₀) × ValidMult M
                    × ((T : 𝓑 → 𝓑) (w : 𝓑) → Tg T w ≤ ((T w ⊕ c) ⊗ M))

\end{code}

The discharge: for a `GoodT`, linearly-bounded functional, the orbit transformer
`Torbit Tg Ta` is `GoodT` — so `Good-Iter`'s hypothesis holds on this class.

\begin{code}

orbit-good-lin : (Tg : 𝕋 (ι ⇒ ι)) → GoodT (ι ⇒ ι) Tg → LinBounded Tg
               → (Ta : 𝕋 ι) → GoodT ι Ta → GoodT ι (Torbit Tg Ta)
orbit-good-lin Tg gTg (c , M , c<ε₀ , (M+ , dbl , M<ε₀) , lin) Ta gTa@(Tapres , Tamono) =
 pres , mono
 where
  mbody : 𝓑 → 𝓑
  mbody b = (b ⊕ c) ⊗ M

  mbody-mono : (b b′ : 𝓑) → b ≤ b′ → mbody b ≤ mbody b′
  mbody-mono b b′ b≤b′ = ⊗-mono-left (⊕-mono-left b≤b′ c) M

  iter-bound : (k : ℕ) (w : 𝓑) → iter Tg Ta k w ≤ iter mbody (Ta w) k
  iter-bound zero     w = ≤-refl (Ta w)
  iter-bound (succ k) w =
   ≤-trans (lin (iter Tg Ta k) w)
           (mbody-mono (iter Tg Ta k w) (iter mbody (Ta w) k) (iter-bound k w))

  pres : (w : 𝓑) → w < ε₀ → Torbit Tg Ta w < ε₀
  pres w w<ε₀ = ≤-trans (≤-S orbit≤) bound<ε₀
   where
    orbit≤ : Torbit Tg Ta w ≤ ((Ta w ⊕ c) ⊗ ω^ (M ⊗ ω))
    orbit≤ = ≤-trans (≤-L-mono (λ k → iter-bound k w))
                     (mbody-orbit-≤ M M+ dbl c (Ta w))

    bound<ε₀ : ((Ta w ⊕ c) ⊗ ω^ (M ⊗ ω)) < ε₀
    bound<ε₀ = ⊗-<-ε₀ (Ta w ⊕ c) (ω^ (M ⊗ ω))
                      (⊕-<-ε₀ (Ta w) c (Tapres w w<ε₀) c<ε₀)
                      (ω^-<-ε₀ (M ⊗ ω) (⊗-<-ε₀ M ω M<ε₀ (tower-<-ε₀ 0)))

  mono : (w w′ : 𝓑) → w ≤ w′ → Torbit Tg Ta w ≤ Torbit Tg Ta w′
  mono w w′ w≤w′ =
   ≤-L-mono (λ k → pr₂ (GoodT-iter Tg Ta gTg gTa k) w w′ w≤w′)

\end{code}

So the recursor's orbit-closure hypothesis is genuinely provable on a real class
via ordinal arithmetic already in the library — concrete evidence that the
`MultHereditaryF` residual is arithmetic. The remaining assembly is to thread
`LinBounded` (and its super-linear extension) through the combinator transformers
and connect to dialogue height.

The backbone of that assembly: `LinBounded` is **closed under the recursor's
orbit**. The orbit of a linearly-bounded functional is again linearly bounded,
with the multiplier climbing `M ↦ ω^(M ⊗ ω)` (still `ValidMult`,
`validMult-orbit`) and the same constant — so a nested recursor whose inner
function is linear stays in the class. (The bound needs no `GoodT` hypothesis: the
domination `iter Tg T k w ≤ iter mbody (T w) k` uses only `LinBounded Tg`.)

\begin{code}

LinBounded-orbit : (Tg : 𝕋 (ι ⇒ ι)) → LinBounded Tg
                 → LinBounded (λ Ta → Torbit Tg Ta)
LinBounded-orbit Tg (c , M , c<ε₀ , vM@(M+ , dbl , M<ε₀) , lin) =
 c , ω^ (M ⊗ ω) , c<ε₀ , validMult-orbit vM , bound
 where
  mbody : 𝓑 → 𝓑
  mbody b = (b ⊕ c) ⊗ M

  mbody-mono : (b b′ : 𝓑) → b ≤ b′ → mbody b ≤ mbody b′
  mbody-mono b b′ b≤b′ = ⊗-mono-left (⊕-mono-left b≤b′ c) M

  iter-bound : (T : 𝓑 → 𝓑) (w : 𝓑) (k : ℕ) → iter Tg T k w ≤ iter mbody (T w) k
  iter-bound T w zero     = ≤-refl (T w)
  iter-bound T w (succ k) =
   ≤-trans (lin (iter Tg T k) w)
           (mbody-mono (iter Tg T k w) (iter mbody (T w) k) (iter-bound T w k))

  bound : (T : 𝓑 → 𝓑) (w : 𝓑) → Torbit Tg T w ≤ ((T w ⊕ c) ⊗ ω^ (M ⊗ ω))
  bound T w = ≤-trans (≤-L-mono (λ k → iter-bound T w k))
                      (mbody-orbit-≤ M M+ dbl c (T w))

\end{code}

Completing the algebra of the linear class: identity and successor are linearly
bounded, and — the composition closure — the composite of two linearly-bounded
functionals is linearly bounded, with the constant accumulating (`c_g ⊕ c_f`) and
the multiplier composing (`M_g ⊗ M_f`). The composition proof is the `MDom-∘`
technique: enlarge the inner constant so `MultAffine.crux` absorbs the outer one,
no `affine-fold`. With `LinBounded-orbit`, the linear functionals thus form a
class closed under identity, successor, composition and the recursor orbit — the
`ι ⇒ ι` transformers a linear first-order term can build.

\begin{code}

LinBounded-id : LinBounded (λ T → T)
LinBounded-id =
 Z , ω , Z<ε₀ , ω-valid , (λ T w → x-≤-x⊗ (T w) ω ω-pos)

LinBounded-S : LinBounded (λ T w → S (T w))
LinBounded-S =
 ι[ 1 ] , ω , ι<ε₀ 1 , ω-valid , (λ T w → x-≤-x⊗ (S (T w)) ω ω-pos)

LinBounded-∘ : (Tf Tg : 𝕋 (ι ⇒ ι)) → LinBounded Tf → LinBounded Tg
             → LinBounded (λ T → Tf (Tg T))
LinBounded-∘ Tf Tg (cf , Mf , cf<ε₀ , vMf@(Mf+ , Mfdbl , Mf<ε₀) , linf)
                   (cg , Mg , cg<ε₀ , vMg@(Mg+ , Mgdbl , Mg<ε₀) , ling) =
 (cg ⊕ cf) , (Mg ⊗ Mf) , ⊕-<-ε₀ cg cf cg<ε₀ cf<ε₀ , validMult-⊗ vMg vMf , bound
 where
  bound : (T : 𝓑 → 𝓑) (w : 𝓑)
        → Tf (Tg T) w ≤ ((T w ⊕ (cg ⊕ cf)) ⊗ (Mg ⊗ Mf))
  bound T w =
   transport (λ z → Tf (Tg T) w ≤ z)
             (⊗-assoc (T w ⊕ (cg ⊕ cf)) Mg Mf) chain
   where
    Y : 𝓑
    Y = (T w ⊕ (cg ⊕ cf)) ⊗ Mg

    TgT≤Y : Tg T w ≤ Y
    TgT≤Y = ≤-trans (ling T w)
              (⊗-mono-left (⊕-mono-right (T w) (⊕-increasing-right cg cf)) Mg)

    cf≤Y : cf ≤ Y
    cf≤Y = ≤-trans (⊕-increasing-left cg cf)
             (≤-trans (⊕-increasing-left (T w) (cg ⊕ cf))
                      (x-≤-x⊗ (T w ⊕ (cg ⊕ cf)) Mg Mg+))

    chain : Tf (Tg T) w ≤ (Y ⊗ Mf)
    chain = ≤-trans (linf (Tg T) w)
              (≤-trans (⊗-mono-left (⊕-mono-left TgT≤Y cf) Mf)
                       (crux Mf Mf+ Mfdbl Y cf cf≤Y))

\end{code}

The other functional a first-order combinator builds and iterates is the
**constant** one — `K a` denotes `λ b → a`, transformer `λ _ → Ta`, which ignores
its argument and so is *not* `LinBounded`. Its orbit is nonetheless trivially
bounded: iterating a constant is constant, so `iter (λ _ → Ta) Ta0 k` is `Ta0`
(`k = 0`) or `Ta` (`k ≥ 1`), hence `≤ Ta0 w ⊕ Ta w < ε₀`. So `orbit-good` holds
for constant functionals too — the recursor's orbit-closure is discharged on the
full **linear + constant** class the combinators generate.

\begin{code}

orbit-good-const : (Ta Ta0 : 𝕋 ι) → GoodT ι Ta → GoodT ι Ta0
                 → GoodT ι (Torbit (λ _ → Ta) Ta0)
orbit-good-const Ta Ta0 (Tapres , Tamono) (Ta0pres , Ta0mono) = pres , mono
 where
  iter-const : (k : ℕ) (w : 𝓑) → iter (λ _ → Ta) Ta0 k w ≤ (Ta0 w ⊕ Ta w)
  iter-const zero     w = ⊕-increasing-right (Ta0 w) (Ta w)
  iter-const (succ k) w = ⊕-increasing-left (Ta0 w) (Ta w)

  pres : (w : 𝓑) → w < ε₀ → Torbit (λ _ → Ta) Ta0 w < ε₀
  pres w w<ε₀ = ≤-trans (≤-S (≤-L (λ k → iter-const k w)))
                        (⊕-<-ε₀ (Ta0 w) (Ta w) (Ta0pres w w<ε₀) (Tapres w w<ε₀))

  mono : (w w′ : 𝓑) → w ≤ w′
       → Torbit (λ _ → Ta) Ta0 w ≤ Torbit (λ _ → Ta) Ta0 w′
  mono w w′ w≤w′ = ≤-L-mono mono-k
   where
    mono-k : (k : ℕ) → iter (λ _ → Ta) Ta0 k w ≤ iter (λ _ → Ta) Ta0 k w′
    mono-k zero     = Ta0mono w w′ w≤w′
    mono-k (succ k) = Tamono w w′ w≤w′

\end{code}

The third recursor-body shape: the **partial recursor's own transformer**
`λ Tν → λ w → C w ⊕ Tν w` (a fixed `C` added on the left), which is what
`Iter f x : ι ⇒ ι` denotes and which is iterated by a *nested* recursor. Its
orbit is left-additive, so `Nested.orbit-left-sup-≤` bounds it by
`(C w ⊗ ω) ⊕ Ta0 w < ε₀`. So `orbit-good` holds for the additive shape too.

\begin{code}

orbit-good-add : (C : 𝕋 ι) → GoodT ι C → (Ta0 : 𝕋 ι) → GoodT ι Ta0
               → GoodT ι (Torbit (λ Tν w → C w ⊕ Tν w) Ta0)
orbit-good-add C Cg@(Cpres , Cmono) Ta0 gTa0@(Ta0pres , Ta0mono) = pres , mono
 where
  A : 𝕋 (ι ⇒ ι)
  A = λ Tν w → C w ⊕ Tν w

  Ag : GoodT (ι ⇒ ι) A
  Ag Tν gTν = GoodT-⊕ C Tν Cg gTν

  step : (w : 𝓑) (k : ℕ) → iter A Ta0 (succ k) w ≤ (C w ⊕ iter A Ta0 k w)
  step w k = ≤-refl (C w ⊕ iter A Ta0 k w)

  pres : (w : 𝓑) → w < ε₀ → Torbit A Ta0 w < ε₀
  pres w w<ε₀ =
   ≤-trans (≤-S (orbit-left-sup-≤ (λ k → iter A Ta0 k w) (C w) (step w)))
           (⊕-<-ε₀ (C w ⊗ ω) (Ta0 w)
                   (⊗-<-ε₀ (C w) ω (Cpres w w<ε₀) (tower-<-ε₀ 0))
                   (Ta0pres w w<ε₀))

  mono : (w w′ : 𝓑) → w ≤ w′ → Torbit A Ta0 w ≤ Torbit A Ta0 w′
  mono w w′ w≤w′ =
   ≤-L-mono (λ k → pr₂ (GoodT-iter A Ta0 Ag gTa0 k) w w′ w≤w′)

\end{code}
