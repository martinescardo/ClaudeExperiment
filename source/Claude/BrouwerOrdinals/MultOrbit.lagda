The multiplicative orbit engine (constructive) — past the `ω^ω` ceiling.

`Claude.BrouwerOrdinals.Orbit` is the *additive* engine: a per-step increment that
adds a fixed code `c` — `a (k+1) ≤ a k ⊕ c` — forces the orbit supremum up by
only one factor of `ω` (`L a ≤ a 0 ⊕ c ⊗ ω`). That is "depth cannot bootstrap"
for the additive case, and it caps a single iteration at one `ω`.

The higher-type climb is *multiplicative*, not additive: iterating a functional
scales the height by a fixed factor `m` per step — `a (k+1) ≤ a k ⊗ m` — and the
factor `m` is itself a sub-`ε₀` ordinal (the height of the functional's body),
not a numeral. The ω-polynomial route (`OmegaPoly`, `PolyAffine`) could only
handle *finite* / `ω^k` factors and so capped at `ω^ω`. Here we prove the
multiplicative engine for an **arbitrary** factor `m < ε₀`:

  if `a (k+1) ≤ a k ⊗ m` for a fixed `m < ε₀`, then `L a ≤ a 0 ⊗ ω^(m ⊗ ω)`,
  and hence `L a < ε₀` whenever `a 0 < ε₀`.

The supremum of the powers `mᵏ` is `ω^(m ⊗ ω)` — one exponentiation of `m ⊗ ω`,
where `m ⊗ ω` climbs into the tower as `m` does. So a fixed-factor iteration,
with the factor any ordinal below `ε₀`, stays below `ε₀`, with no polynomial
ceiling. This is the multiplicative counterpart of `Orbit.orbit-sup-≤`, and the
factor may live anywhere below `ε₀` — exactly what the type-level tower needs of
a *single* level (the open kernel remains: that a functional's per-step factor
genuinely is such an `m`, carried hereditarily).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.BrouwerOrdinals.MultOrbit
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import Claude.BrouwerOrdinals.Order fe
open import Claude.BrouwerOrdinals.Orbit fe using (ι[_] ; ω ; _⊗_)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (ω^_ ; ≤-ω^ ; ⊗-mono-left ; ⊗-mono-right ; Z-left-unit ;
        _<_ ; ε₀ ; ω^-<-ε₀ ; tower ; tower-<-ε₀)
open import Claude.BrouwerOrdinals.Affine fe using (⊗-assoc)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (ω^⊗ ; ⊗-<-ε₀)

\end{code}

The powers of a fixed factor `m`: `mᵏ`, by iterated `⊗` (right-multiplication,
matching the recursion of `⊗`). `pw m 0 = 1` and `pw m (k+1) = pw m k ⊗ m`.

\begin{code}

pw : 𝓑 → ℕ → 𝓑
pw m zero     = S Z
pw m (succ k) = pw m k ⊗ m

\end{code}

Each power is dominated by an `ω`-power: `mᵏ ≤ ω^(m ⊗ ι[k])`. The step uses the
inflationary law `m ≤ ω^ m` (to turn the trailing factor `m` into `ω^ m`) and
the exponent homomorphism `ω^a ⊗ ω^b = ω^(a ⊕ b)`; the exponent
`(m ⊗ ι[k]) ⊕ m` is definitionally `m ⊗ ι[succ k]`.

\begin{code}

pw-≤ : (m : 𝓑) (k : ℕ) → pw m k ≤ ω^ (m ⊗ ι[ k ])
pw-≤ m zero     = ≤-refl (S Z)
pw-≤ m (succ k) =
 transport (pw m (succ k) ≤_) (ω^⊗ (m ⊗ ι[ k ]) m)
   (≤-trans (⊗-mono-left (pw-≤ m k) m)
            (⊗-mono-right (ω^ (m ⊗ ι[ k ])) (≤-ω^ m)))

\end{code}

Hence the supremum of the powers is `ω^(m ⊗ ω)`. The denotational identities
`m ⊗ ω = L (λ k → m ⊗ ι[k])` and `ω^ (L g) = L (λ k → ω^ (g k))` make
`ω^ (m ⊗ ω)` *definitionally* `L (λ k → ω^ (m ⊗ ι[k]))`, so the bound is a
single `≤-L-mono`.

\begin{code}

pw-sup-≤ : (m : 𝓑) → L (pw m) ≤ ω^ (m ⊗ ω)
pw-sup-≤ m = ≤-L-mono (pw-≤ m)

\end{code}

And that supremum is `< ε₀` for every factor `m < ε₀`: `m ⊗ ω < ε₀` (the
multiplicative closure `⊗-<-ε₀`, with `ω = tower 0 < ε₀`), so `ω^(m ⊗ ω) < ε₀`
(`ω^-<-ε₀`). No polynomial ceiling: `m` may be any ordinal below `ε₀`.

\begin{code}

ω<ε₀ : ω < ε₀
ω<ε₀ = tower-<-ε₀ 0

pw-sup-<-ε₀ : (m : 𝓑) → m < ε₀ → L (pw m) < ε₀
pw-sup-<-ε₀ m m<ε₀ =
 ≤-trans (≤-S (pw-sup-≤ m)) (ω^-<-ε₀ (m ⊗ ω) (⊗-<-ε₀ m ω m<ε₀ ω<ε₀))

\end{code}

The engine. Fix an orbit `a : ℕ → 𝓑` and a factor `m` with the multiplicative
per-step bound `a (k+1) ≤ a k ⊗ m`.

\begin{code}

module _ (a : ℕ → 𝓑) (m : 𝓑)
         (step : (k : ℕ) → a (succ k) ≤ (a k ⊗ m))
       where

\end{code}

The `k`-th orbit point is bounded by the start scaled by `mᵏ`. The successor
step multiplies through, associating the accumulated power with the new factor
(`⊗-assoc`); the base case is the right unit `a 0 ⊗ 1 = a 0` (via `Z`-left-unit,
since `a 0 ⊗ S Z` is definitionally `Z ⊕ a 0`).

\begin{code}

 orbit-mult-≤ : (k : ℕ) → a k ≤ (a 0 ⊗ pw m k)
 orbit-mult-≤ zero     =
  transport (a 0 ≤_) ((Z-left-unit (a 0)) ⁻¹) (≤-refl (a 0))
 orbit-mult-≤ (succ k) =
  transport (λ z → a (succ k) ≤ z) (⊗-assoc (a 0) (pw m k) m)
            (≤-trans (step k) (⊗-mono-left (orbit-mult-≤ k) m))

\end{code}

Hence the orbit supremum is bounded by the start scaled by the supremum of the
powers — `L a ≤ a 0 ⊗ L (pw m)` — using `a 0 ⊗ L (pw m) = L (λ k → a 0 ⊗ pw m k)`
definitionally.

\begin{code}

 orbit-mult-sup-≤ : L a ≤ (a 0 ⊗ L (pw m))
 orbit-mult-sup-≤ = ≤-L-mono orbit-mult-≤

\end{code}

The payoff: a fixed-factor multiplicative orbit, with the factor `m < ε₀` and a
sub-`ε₀` start, has supremum `< ε₀`. This is the multiplicative engine for one
level of the type-level tower — reaching *any* factor below `ε₀`, past the
`ω^ω` ceiling of the polynomial route.

\begin{code}

 orbit-mult-<-ε₀ : m < ε₀ → a 0 < ε₀ → L a < ε₀
 orbit-mult-<-ε₀ m<ε₀ a0<ε₀ =
  ≤-trans (≤-S orbit-mult-sup-≤)
          (⊗-<-ε₀ (a 0) (L (pw m)) a0<ε₀ (pw-sup-<-ε₀ m m<ε₀))

\end{code}
