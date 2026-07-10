Attacking the bridge (B): height rides on magnitude (constructive).

The conjecture's residual orbit bound splits (Howard reframing, see
`TwoComponent`) as **(A)** the magnitude orbit grows at rate `< ε₀` (classical
Howard, citable) plus **(B)** the dialogue-native bridge

  height-increment per orbit step `≤ ω^magnitude`,

so that the type-level tower `ω↑↑ℓ` stays `< ε₀`. Concretely (B) decomposes
further into

  **(B1)** the per-step increment is `≤ ω^{eₖ}` (the dialogue content), and
  **(B2)** with `eₖ ≤ β < ε₀` [from (A)] the orbit sum is `< ε₀`.

(B2) is *done*: if `eₖ ≤ β`, then `ω^{eₖ} ≤ ω^β` (fixed), and the orbit engine
(`Orbit.height-iter-from-step`, fixed increment) gives the bound. So the heart
is (B1), and the heart of (B1) is the **tower-step**, proved here:

  *iterating a function whose height-increment is `ω^e` raises the
  height-exponent to `e+1` — one `ω` per nesting level.*

That is exactly `ω↑↑(nesting)`, and it is the precise mechanism by which the
tower climbs. This module proves it (for the fixed-increment case, which is
where the dialogue side is determinate), together with the base increments,
and states precisely the open kernel: that a System T functional's increment
*is* `ω^magnitude` with the magnitude `< ε₀`-bounded — the genuinely
dialogue-specific, hereditary part.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.Bridge
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe
 using (ι[_] ; ω ; _⊗_ ; height-iter-from-step)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (ω^_ ; _<_ ; ε₀ ; ⊕-<-ε₀ ; S-<-ε₀ ; ω^-<-ε₀)

\end{code}

The base increments. The oracle (`generic`) raises the height by one,
i.e. by `ω^0`; this is the `e = 0` base of the tower. (Relabelling `succ'`
is height-free, increment `0`; both are below `ω^0`.)

\begin{code}

Ω-increment : (y : B ℕ) → height (generic y) ≤ (height y ⊕ ω^ ι[ 0 ])
Ω-increment = height-generic

\end{code}

The **tower-step**: if every step of an orbit raises the height by at most
the fixed `ω^e`, then the oracle-driven iteration raises the height-exponent
to `e+1`. (`ω^ι[e] ⊗ ω = ω^ι[e+1]` definitionally, so this is the orbit
engine read in exponent form.) One `ω` per nesting level — the source of
`ω↑↑ℓ`.

\begin{code}

iter-tower-step
 : (f : B ℕ → B ℕ) (x : B ℕ) (e : ℕ)
 → ((k : ℕ) → height (iter f x (succ k)) ≤ (height (iter f x k) ⊕ ω^ ι[ e ]))
 → (n : B ℕ)
 → height (kleisli-extension (iter f x) n)
   ≤ ((height x ⊕ ω^ ι[ succ e ]) ⊕ height n)
iter-tower-step f x e step n = height-iter-from-step f x (ω^ ι[ e ]) step n

\end{code}

Reading the chain. Starting from the oracle at exponent `0` (`Ω-increment`),
each ground iteration that uses the oracle as its *count* applies one
`iter-tower-step`, taking exponent `e ↦ e+1`. A first-order term nests these
finitely, so its height-exponent is a *finite* `e`, giving height
`< ω^{e+1} ≤ ω^ω` — exactly the first-order ceiling. Each higher *type* level
lets the exponent itself become an ordinal `< ε₀` rather than a numeral, so
the tower runs `ω, ω^ω, ω^{ω^ω}, …` with `ε₀` the supremum.

The open kernel (B1, genuinely dialogue-specific): for a System T functional
`f`, the per-step increment hypothesis above holds with `e` bounded by the
*magnitude* of `f`'s internal iteration counts — and that magnitude is
`< ε₀` by Howard (A). Establishing "increment `= ω^magnitude`" hereditarily,
so that `e` at type level `ℓ` is the ordinal driving `ω↑↑ℓ`, is the residual
content. The tower-step here is its engine; the magnitude bound is its (A).

The tower-step above fixes the exponent to a *numeral* `ι[e]`, which caps the
climb at the first-order ceiling `ω^ω` (finite exponents). The **full**
conjecture needs the exponent itself to be an ordinal `< ε₀` — one `ω`-power
per type level, with the exponent at level `ℓ` the sub-`ε₀` ordinal `tower ℓ`
rather than a finite `e`. The engine is exponent-agnostic: `height-iter-from-step`
takes *any* fixed increment code, and `ω^ (S e) ＝ ω^ e ⊗ ω` definitionally,
so the same one-line proof generalizes verbatim to a Brouwer-code exponent
`e : 𝓑`. Iterating a function whose per-step increment is `ω^ e` raises the
height-exponent to `S e`.

\begin{code}

iter-tower-step-code
 : (f : B ℕ → B ℕ) (x : B ℕ) (e : 𝓑)
 → ((k : ℕ) → height (iter f x (succ k)) ≤ (height (iter f x k) ⊕ ω^ e))
 → (n : B ℕ)
 → height (kleisli-extension (iter f x) n)
   ≤ ((height x ⊕ ω^ (S e)) ⊕ height n)
iter-tower-step-code f x e step n = height-iter-from-step f x (ω^ e) step n

\end{code}

And now the ε₀ accounting closes for the *ordinal-exponent* step, exactly as
it did for the numeral one — using that `ε₀` is closed under successor,
`ω`-exponentiation, and `⊕` (`Epsilon0.S-<-ε₀, ω^-<-ε₀, ⊕-<-ε₀`). Given a
per-step increment `ω^ e` with the exponent `e < ε₀`, and sub-`ε₀` heights for
the start `x` and the count `n`, the oracle-driven iteration has height
`< ε₀`. This is the higher-type tower mechanism as a machine-checked theorem —
*conditional*, honestly, on the open kernel (B1): that a System T functional's
per-step increment genuinely is `ω^ e` with `e < ε₀` (the dialogue-native,
hereditary content, still unproved). What is proved is that *given* that
increment shape, the climb stays below `ε₀` at every type level, not just the
first.

\begin{code}

iter-tower-step-<-ε₀
 : (f : B ℕ → B ℕ) (x : B ℕ) (e : 𝓑) → e < ε₀
 → ((k : ℕ) → height (iter f x (succ k)) ≤ (height (iter f x k) ⊕ ω^ e))
 → (n : B ℕ) → height x < ε₀ → height n < ε₀
 → height (kleisli-extension (iter f x) n) < ε₀
iter-tower-step-<-ε₀ f x e e<ε₀ step n hx hn =
 ≤-trans (≤-S (iter-tower-step-code f x e step n))
         (⊕-<-ε₀ (height x ⊕ ω^ (S e)) (height n)
                 (⊕-<-ε₀ (height x) (ω^ (S e)) hx
                         (ω^-<-ε₀ (S e) (S-<-ε₀ e e<ε₀)))
                 hn)

\end{code}

Specialising `e` to a numeral recovers the first-order tower-step, and letting
`e = tower ℓ` gives the `ω↑↑(ℓ+1)` step of the full climb; the engine no longer
distinguishes the two — only the open kernel (B1), which supplies the exponent
`e` for a given functional, does.
