The first-order fundamental theorem, unconditionally, for the single-argument
(S-diagonal-free) fragment.

Every result so far bounding a dialogue-tree height by `ε₀` has been
*conditional* — on an orbit bound (`Conditional`), a per-step increment
(`Orbit`, `Bridge`), a graft bound (`Nested`), or the affine shape of a
majorant (`Hereditary`, `PolyTransformer`). This module proves an
**unconditional** `height < ε₀`, for a genuine fragment of System T closed
under the recursor.

The fragment is the **single-argument first-order fragment**: every function
has type `ι ⇒ ι`. Ground terms are `Zero` and applications; functions are the
oracle `Ω`, `Succ`, partial recursors `Iter f x`, **composition** `f ∘ g`, and
**constants** `λ _ → x` (the ground `K`). What is excluded is precisely the
`S` *diagonal* `λ a → φ a (γ a)`, which shares one argument between a function
and its argument and so forces a multi-argument *joint* affine bound — the
persistent wall. Everything here stays in the single-argument affine class
`Aff` (`AffineClosure`), closed under composition (`Aff-∘`), application
(`Aff-app`), constants (`const-Aff`) and partial iteration (`Aff-Iter-partial`).
So no joint bound is ever needed and the theorem goes through in full — for a
fragment that already contains arbitrary compositions, constants, and nested
recursion, not merely single applications.

The exponents here are finite, so the bound is in fact `< ω^ω`; the `< ε₀`
statement is what the `Aff` machinery delivers directly. Lifting past the `S`
diagonal (hence to all of `T₁`, and to `ε₀` proper via higher types) is the
open hereditary closure; this is the maximal fragment that closes with the
single-argument affine class alone.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.Applicative
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Conditional fe
open import Claude.BrouwerOrdinals.Epsilon0 fe using (_<_ ; ε₀ ; ⊕-mono-right)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (Aff ; Aff-id ; Aff-S ; Aff-app ; Aff-∘ ; const-Aff ; Aff-Iter-partial ; Z<ε₀)

\end{code}

The applicative first-order syntax, in two mutually recursive sorts: ground
terms `Gnd` (type `ι`) and unary functions `Fun` (type `ι ⇒ ι`). A ground term
is `Zero` or a function applied to a ground term; a function is the oracle
`Ω`, `Succ`, or a partial recursor `Iter f x`.

\begin{code}

data Gnd : 𝓤₀ ̇
data Fun : 𝓤₀ ̇

data Gnd where
 zeroG : Gnd
 appG  : Fun → Gnd → Gnd

data Fun where
 ΩF     : Fun
 succF  : Fun
 iterF  : Fun → Gnd → Fun
 compF  : Fun → Fun → Fun
 constF : Gnd → Fun

\end{code}

Their interpretation into the dialogue model. `appG f x` is application;
`iterF f x` is `λ ν → iter' f x ν = kleisli-extension (iter f x)` at type `ι`.

\begin{code}

⟦_⟧G : Gnd → B ℕ
⟦_⟧F : Fun → (B ℕ → B ℕ)

⟦ zeroG ⟧G   = η 0
⟦ appG f x ⟧G = ⟦ f ⟧F ⟦ x ⟧G

⟦ ΩF ⟧F        = generic
⟦ succF ⟧F     = B-functor succ
⟦ iterF f x ⟧F = kleisli-extension (iter ⟦ f ⟧F ⟦ x ⟧G)
⟦ compF f g ⟧F = λ d → ⟦ f ⟧F (⟦ g ⟧F d)
⟦ constF x ⟧F  = λ _ → ⟦ x ⟧G

\end{code}

The height majorants. Ground terms get a Brouwer code; functions get a
height-transform. The recursor's majorant is the orbit supremum plus the
count, as in `Majorant`.

\begin{code}

μG : Gnd → 𝓑
μF : Fun → (𝓑 → 𝓑)

μG zeroG     = Z
μG (appG f x) = μF f (μG x)

μF ΩF          = λ a → S a
μF succF       = λ a → a
μF (iterF f x) = λ ν → L (λ k → iter (μF f) (μG x) k) ⊕ ν
μF (compF f g) = λ a → μF f (μF g a)
μF (constF x)  = λ _ → μG x

\end{code}

Every function majorant is affine, and every ground majorant is `< ε₀`. This
is the crux: it is proved by a single mutual induction, with the recursor
cases discharged by `Aff-Iter-partial` (a partial recursor is affine) and
`Aff-app` (an affine function at a sub-`ε₀` input is `< ε₀`) — no joint bound
required, because there is only ever one ground argument in play.

\begin{code}

Aff-μF  : (f : Fun) → Aff (μF f)
good-μG : (x : Gnd) → μG x < ε₀

Aff-μF ΩF          = Aff-S
Aff-μF succF       = Aff-id
Aff-μF (iterF f x) = Aff-Iter-partial (Aff-μF f) (μG x) (good-μG x)
Aff-μF (compF f g) = Aff-∘ (Aff-μF f) (Aff-μF g)
Aff-μF (constF x)  = const-Aff (μG x) (good-μG x)

good-μG zeroG     = Z<ε₀
good-μG (appG f x) = Aff-app (Aff-μF f) (μG x) (good-μG x)

\end{code}

The majorization (the logical relation, restricted to the fragment): a ground
term's height is `≤` its majorant, and a function preserves the height bound as
its majorant transforms it. Mutually recursive; the recursor case bounds the
orbit termwise by the majorant orbit, hence uniformly by its supremum, and
closes with the conditional recursor bound `height-iter-≤-orbit-bound`.

\begin{code}

R-G : (x : Gnd) → height ⟦ x ⟧G ≤ μG x
R-F : (f : Fun) (d : B ℕ) (a : 𝓑) → height d ≤ a → height (⟦ f ⟧F d) ≤ μF f a

R-G zeroG     = ≤-Z
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

\end{code}

The theorem: every ground term of the applicative first-order fragment has
dialogue-tree height `< ε₀` — unconditionally.

\begin{code}

height-<-ε₀ : (x : Gnd) → height ⟦ x ⟧G < ε₀
height-<-ε₀ x = ≤-trans (≤-S (R-G x)) (good-μG x)

\end{code}

In particular a first-order dialogue tree `⟦ appG (iterF f x) n ⟧G =
kleisli-extension (iter ⟦ f ⟧F ⟦ x ⟧G) ⟦ n ⟧G` — the recursor driven by an
arbitrary ground count — has height `< ε₀`, with the count `⟦ n ⟧G` allowed to
be an oracle read (`appG ΩF zeroG`, magnitude unbounded, so the orbit sup is
genuinely taken). This is the unconditional recursor case at first order.

\begin{code}

height-recursor-<-ε₀ : (f : Fun) (x n : Gnd)
                     → height (kleisli-extension (iter ⟦ f ⟧F ⟦ x ⟧G) ⟦ n ⟧G) < ε₀
height-recursor-<-ε₀ f x n = height-<-ε₀ (appG (iterF f x) n)

\end{code}
