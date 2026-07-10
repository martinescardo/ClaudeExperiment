The first-order fundamental theorem, unconditionally, for a fragment that
*includes* the recursor `S`-diagonal — the canonical tower-driving term.

`Applicative` proved `height < ε₀` unconditionally for the single-argument
first-order fragment, but deliberately *excluded* the `S`-diagonal
`λ a → φ a (γ a)` (the shared argument that forces a multi-argument joint
bound). That exclusion was the persistent wall: the affine class `Aff` iterates
only via `affine-fold`, which fails for a limit multiplier, so a start-varying
recursor reused as a two-argument function escaped the class.

`MultDominated` removed the wall at the majorant level: the multiplier-dominated
class `MDom` is closed under composition (`MDom-∘`), the recursor orbit
(`MDom-orbit`), and the recursor `S`-diagonal (`MDom-recursor-diag`,
`λ x → Iter φ x (G x)` — iterate `φ` from the bound variable `x` for `G x`
steps). This module cashes that in on real dialogue trees: the same
`Applicative` skeleton — concrete syntax, interpretation into the dialogue
model, height majorants, and a logical relation — but with `Aff` replaced by
`MDom` and a new constructor `iterDiagF` for the recursor `S`-diagonal. The
theorem `height-<-ε₀` is again unconditional.

Honest scope. This is still a *fragment*, not all of first-order System T: the
functions are those `MDom` is closed under, and `iterDiagF` is the specific
`S`-diagonal `MDom-recursor-diag` handles (start = the bound variable, count a
function of it). It is strictly larger than `Applicative`'s fragment — it adds
the previously-walled tower-driving term — and every majorant here climbs the
multiplier tower (`M_ψ ⊗ M_φ`, `ω^(M ⊗ ω)`, `M_G ⊗ M`) yet stays `< ε₀`. What
remains for the full conjecture is the type-indexed hereditary assembly over
*all* first-order types (function arguments à la Howard, `K`/`S` at higher
types) — structural plumbing, with every arithmetic closure now in hand.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultApplicative
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Conditional fe
open import Claude.BrouwerOrdinals.Epsilon0 fe using (_<_ ; ε₀ ; ⊕-mono-right)
open import Claude.BrouwerOrdinals.AffineClosure fe using (Z<ε₀)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (MDom ; MDom-id ; MDom-succ ; MDom-∘ ; MDom-const ; MDom-const-left ;
        MDom-recursor-diag ; MDom-app ; MDom-orbit-<-ε₀)

\end{code}

The syntax, in two mutually recursive sorts. A ground term `Gnd` (type `ι`) is
`Zero` or a function applied to a ground term. A function `Fun` (type `ι ⇒ ι`)
is the oracle `Ω`, `Succ`, a partial recursor `iterF f x` (fixed start `x`,
variable count), a composition `compF f g`, a constant `constF x`, or — the new
constructor — the recursor `S`-diagonal `iterDiagF φ G`, which iterates `φ` from
its *own* argument for `G` of that argument steps.

\begin{code}

data Gnd : 𝓤₀ ̇
data Fun : 𝓤₀ ̇

data Gnd where
 zeroG : Gnd
 appG  : Fun → Gnd → Gnd

data Fun where
 ΩF        : Fun
 succF     : Fun
 iterF     : Fun → Gnd → Fun
 compF     : Fun → Fun → Fun
 constF    : Gnd → Fun
 iterDiagF : Fun → Fun → Fun

\end{code}

Interpretation into the dialogue model. `iterF f x` is `λ ν → iter' f x ν =
kleisli-extension (iter f x)` at type `ι`; `iterDiagF φ G` interprets its
argument `d` as *both* the recursor's start and (through `G`) its count:
`λ d → kleisli-extension (iter ⟦φ⟧ d) (⟦G⟧ d)`.

\begin{code}

⟦_⟧G : Gnd → B ℕ
⟦_⟧F : Fun → (B ℕ → B ℕ)

⟦ zeroG ⟧G    = η 0
⟦ appG f x ⟧G = ⟦ f ⟧F ⟦ x ⟧G

⟦ ΩF ⟧F            = generic
⟦ succF ⟧F         = B-functor succ
⟦ iterF f x ⟧F     = kleisli-extension (iter ⟦ f ⟧F ⟦ x ⟧G)
⟦ compF f g ⟧F     = λ d → ⟦ f ⟧F (⟦ g ⟧F d)
⟦ constF x ⟧F      = λ _ → ⟦ x ⟧G
⟦ iterDiagF φ G ⟧F = λ d → kleisli-extension (iter ⟦ φ ⟧F d) (⟦ G ⟧F d)

\end{code}

The height majorants. Ground terms get a Brouwer code; functions get a
height-transform. The recursor's majorant is the orbit supremum plus the count:
for `iterF f x` the orbit is over the *fixed* start `μG x`, for `iterDiagF φ G`
it is over the *bound variable* `a`, and the count is `μF G a`.

\begin{code}

μG : Gnd → 𝓑
μF : Fun → (𝓑 → 𝓑)

μG zeroG      = Z
μG (appG f x) = μF f (μG x)

μF ΩF            = λ a → S a
μF succF         = λ a → a
μF (iterF f x)   = λ ν → L (λ k → iter (μF f) (μG x) k) ⊕ ν
μF (compF f g)   = λ a → μF f (μF g a)
μF (constF x)    = λ _ → μG x
μF (iterDiagF φ G) = λ a → L (λ k → iter (μF φ) a k) ⊕ μF G a

\end{code}

Every function majorant is `MDom`, and every ground majorant is `< ε₀`. One
mutual induction, each case a single `MDom` closure: `Ω`/`Succ` the additive
leaves, `iterF` the left-additive partial recursor (`MDom-const-left`, its
orbit `< ε₀` by `MDom-orbit-<-ε₀`), `compF` composition, `constF` the constant
leaf, and — the new case — `iterDiagF` the recursor `S`-diagonal by
`MDom-recursor-diag`.

\begin{code}

MDom-μF : (f : Fun) → MDom (μF f)
good-μG : (x : Gnd) → μG x < ε₀

MDom-μF ΩF          = MDom-succ
MDom-μF succF       = MDom-id
MDom-μF (iterF f x) =
 MDom-const-left (L (λ k → iter (μF f) (μG x) k))
                 (MDom-orbit-<-ε₀ (MDom-μF f) (μG x) (good-μG x))
MDom-μF (compF f g)     = MDom-∘ (MDom-μF f) (MDom-μF g)
MDom-μF (constF x)      = MDom-const (μG x) (good-μG x)
MDom-μF (iterDiagF φ G) = MDom-recursor-diag (MDom-μF φ) (MDom-μF G)

good-μG zeroG      = Z<ε₀
good-μG (appG f x) = MDom-app (MDom-μF f) (μG x) (good-μG x)

\end{code}

The majorization (the logical relation): a ground term's height is `≤` its
majorant, and a function preserves the height bound as its majorant transforms
it. The two recursor cases bound the orbit termwise by the majorant orbit,
hence uniformly by its supremum, and close with the conditional recursor bound
`height-iter-≤-orbit-bound`. For `iterDiagF` the orbit is over the argument `d`
(base case `h : height d ≤ a`) and the count is `⟦G⟧ d`.

\begin{code}

R-G : (x : Gnd) → height ⟦ x ⟧G ≤ μG x
R-F : (f : Fun) (d : B ℕ) (a : 𝓑) → height d ≤ a → height (⟦ f ⟧F d) ≤ μF f a

R-G zeroG      = ≤-Z
R-G (appG f x) = R-F f ⟦ x ⟧G (μG x) (R-G x)

R-F ΩF    d a h = ≤-trans (height-generic d) (≤-S h)
R-F succF d a h = transport (_≤ a) ((height-B-functor-succ d) ⁻¹) h
R-F (iterF f x) d a h =
 ≤-trans (height-iter-≤-orbit-bound ⟦ f ⟧F ⟦ x ⟧G orbit uniform d)
         (⊕-mono-right orbit h)
 where
  orbit : 𝓑
  orbit = L (λ k → iter (μF f) (μG x) k)

  orbit-pt : (k : ℕ) → height (iter ⟦ f ⟧F ⟦ x ⟧G k) ≤ iter (μF f) (μG x) k
  orbit-pt zero     = R-G x
  orbit-pt (succ k) =
   R-F f (iter ⟦ f ⟧F ⟦ x ⟧G k) (iter (μF f) (μG x) k) (orbit-pt k)

  uniform : (k : ℕ) → height (iter ⟦ f ⟧F ⟦ x ⟧G k) ≤ orbit
  uniform k = ≤-trans (orbit-pt k) (≤-L-upper-bound (λ k → iter (μF f) (μG x) k) k)
R-F (compF f g) d a h = R-F f (⟦ g ⟧F d) (μF g a) (R-F g d a h)
R-F (constF x)  d a h = R-G x
R-F (iterDiagF φ G) d a h =
 ≤-trans (height-iter-≤-orbit-bound ⟦ φ ⟧F d orbit uniform (⟦ G ⟧F d))
         (⊕-mono-right orbit (R-F G d a h))
 where
  orbit : 𝓑
  orbit = L (λ k → iter (μF φ) a k)

  orbit-pt : (k : ℕ) → height (iter ⟦ φ ⟧F d k) ≤ iter (μF φ) a k
  orbit-pt zero     = h
  orbit-pt (succ k) =
   R-F φ (iter ⟦ φ ⟧F d k) (iter (μF φ) a k) (orbit-pt k)

  uniform : (k : ℕ) → height (iter ⟦ φ ⟧F d k) ≤ orbit
  uniform k = ≤-trans (orbit-pt k) (≤-L-upper-bound (λ k → iter (μF φ) a k) k)

\end{code}

The theorem: every ground term of this fragment — which includes the recursor
`S`-diagonal — has dialogue-tree height `< ε₀`, unconditionally.

\begin{code}

height-<-ε₀ : (x : Gnd) → height ⟦ x ⟧G < ε₀
height-<-ε₀ x = ≤-trans (≤-S (R-G x)) (good-μG x)

\end{code}

In particular the recursor `S`-diagonal driven by an arbitrary ground count —
`⟦ appG (iterDiagF φ G) n ⟧G = kleisli-extension (iter ⟦φ⟧ ⟦n⟧) (⟦G⟧ ⟦n⟧)`, the
count `⟦ n ⟧` allowed to be an oracle read so the orbit sup is genuinely taken
— has height `< ε₀`. This is the tower-driving term `Applicative` could not
reach, now unconditional.

\begin{code}

height-recursor-diag-<-ε₀ : (φ G : Fun) (n : Gnd)
                          → height (kleisli-extension (iter ⟦ φ ⟧F ⟦ n ⟧G) (⟦ G ⟧F ⟦ n ⟧G)) < ε₀
height-recursor-diag-<-ε₀ φ G n = height-<-ε₀ (appG (iterDiagF φ G) n)

\end{code}
