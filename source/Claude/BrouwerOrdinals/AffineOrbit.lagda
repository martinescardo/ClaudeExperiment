The ω-affine orbit, for an arbitrary sub-`ε₀` multiplier (constructive).

`Affine.affine-orbit-<-ε₀` bounds the orbit of an affine majorant
`φ b ≤ (b ⊕ d) ⊗ ι[p+1]` — but only for a **finite** multiplier `ι[p+1]`. The
higher-type climb needs the multiplier to be an ordinal `m < ε₀` (the height of
the iterated functional's body), and there the proof of `Affine` breaks: it
folds the constant inside via `affine-fold` (`x ⊗ m ⊕ d ≤ (x ⊕ d) ⊗ m`), which
is provably **false** for a limit `m` (`(ω ⊗ ω) ⊕ 1 = ω²+1 > ω²`). That failure
is what pinned the whole hereditary development at the `ω^ω` ceiling.

The multiplicative engine `MultOrbit` removes the ceiling for a *pure* factor
(`a (k+1) ≤ a k ⊗ m`, any `m < ε₀`). This module reduces the **affine** orbit
to that pure engine, *without* the fold lemma. The idea: dominate the affine
orbit by the pure-multiplicative majorant `maj a k = (a ⊕ d) ⊗ mᵏ`. The one
fact that makes the constant `d` disappear is that a limit `m` **absorbs finite
left-multiplication** — `ι[2] ⊗ m ≤ m` (true for every `ω`-power). Then, once
`b ≥ d`,

  `(b ⊕ d) ⊗ m  ≤  (b ⊕ b) ⊗ m  =  (b ⊗ ι[2]) ⊗ m  =  b ⊗ (ι[2] ⊗ m)  ≤  b ⊗ m`,

so each affine step is dominated by one pure-multiplicative step. The majorant
`maj a` stays `≥ d` by construction, so the domination is uniform, and
`MultOrbit.orbit-mult-<-ε₀` gives `sup_k φᵏ a < ε₀` — for **any** multiplier
`m < ε₀` (a limit), past the `ω^ω` ceiling.

This is exactly the recursor case the hereditary predicate needs, with an
ordinal (not finite) multiplier. The absorption hypothesis `ι[2] ⊗ m ≤ m` is
discharged below for `m = ω` and for every `m = ω^ e` with `e` absorbing `1`
(`ι[1] ⊕ e ≤ e`, i.e. `e ≥ ω`) — i.e. at every level of the tower.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.BrouwerOrdinals.AffineOrbit
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import Claude.BrouwerOrdinals.Order fe
open import Claude.BrouwerOrdinals.Orbit fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ⊕-<-ε₀ ; ⊕-mono-right ; ⊕-increasing-right ;
        ⊗-mono-left ; ⊗-mono-right ; Z-left-unit ; ω^_ ; ω^-mono ; ω^-ι1)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊗-assoc ; ⊕-increasing-left ; ι-*-homo ; _·ℕ_)
open import Claude.BrouwerOrdinals.AffineClosure fe using (x-≤-x⊗)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (ω^⊗)
open import Claude.BrouwerOrdinals.MultOrbit fe using (orbit-mult-<-ε₀)

\end{code}

The finite absorption hypothesis is satisfiable at every relevant multiplier.
For `m = ω`: `ι[2] ⊗ ι[n] = ι[2n] ≤ ω`. For `m = ω^ e` with `e` absorbing `1`
(`ι[1] ⊕ e ≤ e`, i.e. `e` infinite): `ι[2] ⊗ ω^ e ≤ ω ⊗ ω^ e = ω^(ι[1] ⊕ e) ≤
ω^ e` (exponent homomorphism `ω^⊗` and `ω = ω^ι[1]`).

\begin{code}

ι2⊗ω-≤-ω : (ι[ 2 ] ⊗ ω) ≤ ω
ι2⊗ω-≤-ω = ≤-L (λ n → transport (_≤ ω) ((ι-*-homo 2 n) ⁻¹)
                                (≤-L-upper-bound ι[_] (2 ·ℕ n)))

fin-abs : (e : 𝓑) → (ι[ 1 ] ⊕ e) ≤ e → (ι[ 2 ] ⊗ ω^ e) ≤ ω^ e
fin-abs e habs =
 ≤-trans (⊗-mono-left (≤-L-upper-bound ι[_] 2) (ω^ e))
         (transport (_≤ ω^ e) step (ω^-mono habs))
 where
  step : ω^ (ι[ 1 ] ⊕ e) ＝ (ω ⊗ ω^ e)
  step = (ω^⊗ ι[ 1 ] e) ⁻¹ ∙ ap (_⊗ ω^ e) ω^-ι1

\end{code}

Doubling is `⊗ ι[2]`: `x ⊕ x = x ⊗ ι[2]` (definitionally `(Z ⊕ x) ⊕ x`, up to
the left unit).

\begin{code}

⊕-self : (x : 𝓑) → (x ⊕ x) ＝ (x ⊗ ι[ 2 ])
⊕-self x = ap (_⊕ x) ((Z-left-unit x) ⁻¹)

\end{code}

Fix the affine data: a majorant `φ` with `φ b ≤ (b ⊕ d) ⊗ m`, a positive
multiplier (`S Z ≤ m`) that absorbs finite left-multiplication (`ι[2] ⊗ m ≤ m`).

\begin{code}

module _ (φ : 𝓑 → 𝓑) (d m : 𝓑)
         (SZ≤m     : S Z ≤ m)
         (m-abs    : (ι[ 2 ] ⊗ m) ≤ m)
         (φ-affine : (b : 𝓑) → φ b ≤ ((b ⊕ d) ⊗ m))
       where

\end{code}

The pure-multiplicative majorant `maj a k = (a ⊕ d) ⊗ mᵏ`, and the key step:
once `b ≥ d`, the affine step `(b ⊕ d) ⊗ m` is dominated by the pure step
`b ⊗ m` (double, associate, absorb).

\begin{code}

 maj : 𝓑 → ℕ → 𝓑
 maj a = iter (λ b → b ⊗ m) (a ⊕ d)

 key-step : (b : 𝓑) → d ≤ b → ((b ⊕ d) ⊗ m) ≤ (b ⊗ m)
 key-step b d≤b =
  ≤-trans (⊗-mono-left b⊕d≤b⊗2 m)
          (transport (_≤ (b ⊗ m)) ((⊗-assoc b ι[ 2 ] m) ⁻¹)
                     (⊗-mono-right b m-abs))
  where
   b⊕d≤b⊗2 : (b ⊕ d) ≤ (b ⊗ ι[ 2 ])
   b⊕d≤b⊗2 = transport ((b ⊕ d) ≤_) (⊕-self b) (⊕-mono-right b d≤b)

\end{code}

The majorant stays `≥ d` (it starts at `a ⊕ d ≥ d` and only grows), and it
dominates the true orbit `iter φ a`.

\begin{code}

 d≤maj : (a : 𝓑) (k : ℕ) → d ≤ maj a k
 d≤maj a zero     = ⊕-increasing-left a d
 d≤maj a (succ k) = ≤-trans (d≤maj a k) (x-≤-x⊗ (maj a k) m SZ≤m)

 dom : (a : 𝓑) (k : ℕ) → iter φ a k ≤ maj a k
 dom a zero     = ⊕-increasing-right a d
 dom a (succ k) =
  ≤-trans (φ-affine (iter φ a k))
          (≤-trans (⊗-mono-left (⊕-mono-left (dom a k) d) m)
                   (key-step (maj a k) (d≤maj a k)))

\end{code}

The payoff: the ω-affine orbit is `< ε₀` for the multiplier `m < ε₀`. The
dominating majorant is a pure-multiplicative orbit, handled by `MultOrbit`; the
true orbit sits below it. No `ω^ω` ceiling: `m` may be any limit below `ε₀`.

\begin{code}

 affine-orbit-ordinal-<-ε₀
  : (a : 𝓑) → m < ε₀ → a < ε₀ → d < ε₀ → L (λ k → iter φ a k) < ε₀
 affine-orbit-ordinal-<-ε₀ a m<ε₀ a<ε₀ d<ε₀ =
  ≤-trans (≤-S (≤-L-mono (dom a)))
          (orbit-mult-<-ε₀ (maj a) m (λ k → ≤-refl (maj a k ⊗ m)) m<ε₀
                           (⊕-<-ε₀ a d a<ε₀ d<ε₀))

\end{code}
