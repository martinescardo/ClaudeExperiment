Brouwer-code arithmetic toward ε₀ (constructive).

This module builds the ordinal-arithmetic toolkit on Brouwer codes needed to
turn the orbit engine's output code (`Claude.BrouwerOrdinals.Orbit`) into a
genuine `< ε₀` statement — sub-development (I) of
`dialogue-tree-height-frontier.md`. The constructive height file supplies
only `⊕`; the orbit file added `ι[_], ω, _⊗_`. Here we add base-`ω`
exponentiation `ω^_`, the ε₀ tower, the strict order, and the monotonicity
laws, all `--safe --without-K`.

This is *standard* ordinal arithmetic (not dialogue-specific); it is the
price of working with explicit codes rather than citing the textbook
`ε₀`-closure facts. What is proved here: left-unit and monotonicity of `⊕`
and `⊗`, monotonicity of `ω^_` in the exponent, and `a < tower n ⟹ a < ε₀`.
The genuinely fiddly principality facts (`a,b < ω^ω ⟹ a⊕b < ω^ω`, and
`ω^ω ⊗ ω < ε₀`) are flagged at the end as the remaining work; everything
preceding them is complete.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.BrouwerOrdinals.Epsilon0
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import Claude.BrouwerOrdinals.Order fe
open import Claude.BrouwerOrdinals.Orbit fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left ; ⊕-assoc)

\end{code}

The successor is increasing, and the right summand of `⊕` is increasing:
`a ≤ S a` and `a ≤ a ⊕ b`.

\begin{code}

S-increasing : (a : 𝓑) → a ≤ S a
S-increasing Z     = ≤-Z
S-increasing (S a) = ≤-S (S-increasing a)
S-increasing (L f) = ≤-L (λ n → ≤-trans (S-increasing (f n))
                                         (≤-S (≤-L-upper-bound f n)))

⊕-increasing-right : (a b : 𝓑) → a ≤ (a ⊕ b)
⊕-increasing-right a Z     = ≤-refl a
⊕-increasing-right a (S b) = ≤-trans (⊕-increasing-right a b) (S-increasing (a ⊕ b))
⊕-increasing-right a (L f) = ≤-ℓ 0 (⊕-increasing-right a (f 0))

\end{code}

`⊕` is monotone in its right argument; `Z` is its left unit.

\begin{code}

⊕-mono-right : (a : 𝓑) {b c : 𝓑} → b ≤ c → (a ⊕ b) ≤ (a ⊕ c)
⊕-mono-right a {b}     {c}   ≤-Z       = ⊕-increasing-right a c
⊕-mono-right a         (≤-S p)         = ≤-S (⊕-mono-right a p)
⊕-mono-right a         (≤-ℓ n p)       = ≤-ℓ n (⊕-mono-right a p)
⊕-mono-right a         (≤-L p)         = ≤-L (λ n → ⊕-mono-right a (p n))

Z-left-unit : (a : 𝓑) → (Z ⊕ a) ＝ a
Z-left-unit Z     = refl
Z-left-unit (S a) = ap S (Z-left-unit a)
Z-left-unit (L f) = ap L (dfunext fe (λ n → Z-left-unit (f n)))

\end{code}

`⊗` is monotone in each argument.

\begin{code}

⊗-mono-left : {a a′ : 𝓑} → a ≤ a′ → (c : 𝓑) → (a ⊗ c) ≤ (a′ ⊗ c)
⊗-mono-left p Z     = ≤-Z
⊗-mono-left {a} {a′} p (S c) =
 ≤-trans (⊕-mono-left (⊗-mono-left p c) a) (⊕-mono-right (a′ ⊗ c) p)
⊗-mono-left p (L f) = ≤-L-mono (λ n → ⊗-mono-left p (f n))

⊗-mono-right : (a : 𝓑) {b c : 𝓑} → b ≤ c → (a ⊗ b) ≤ (a ⊗ c)
⊗-mono-right a ≤-Z       = ≤-Z
⊗-mono-right a (≤-S p)   = ⊕-mono-left (⊗-mono-right a p) a
⊗-mono-right a (≤-ℓ n p) = ≤-ℓ n (⊗-mono-right a p)
⊗-mono-right a (≤-L p)   = ≤-L (λ n → ⊗-mono-right a (p n))

\end{code}

Base-`ω` exponentiation, and the ε₀ tower.

\begin{code}

ω^_ : 𝓑 → 𝓑
ω^ Z     = S Z
ω^ (S a) = (ω^ a) ⊗ ω
ω^ (L f) = L (λ n → ω^ (f n))

tower : ℕ → 𝓑
tower zero     = ω
tower (succ n) = ω^ (tower n)

ε₀ : 𝓑
ε₀ = L tower

\end{code}

The strict order, and the key entry point: anything below some finite tower
level is below ε₀.

\begin{code}

_<_ : 𝓑 → 𝓑 → 𝓤₀ ̇
a < b = S a ≤ b

infix 4 _<_

<-ε₀-from-tower : (n : ℕ) (a : 𝓑) → a < tower n → a < ε₀
<-ε₀-from-tower n a p = ≤-ℓ n p

\end{code}

One is below every `ω`-power, and `ω^_` is monotone in the exponent.

\begin{code}

one-≤-ω^ : (b : 𝓑) → S Z ≤ ω^ b
one-≤-ω^ Z     = ≤-refl (S Z)
one-≤-ω^ (S b) = ≤-ℓ 1 (transport (S Z ≤_) ((Z-left-unit (ω^ b)) ⁻¹) (one-≤-ω^ b))
one-≤-ω^ (L f) = ≤-ℓ 0 (one-≤-ω^ (f 0))

ω^-mono : {a b : 𝓑} → a ≤ b → ω^ a ≤ ω^ b
ω^-mono {Z}    {b} ≤-Z       = one-≤-ω^ b
ω^-mono            (≤-S p)   = ⊗-mono-left (ω^-mono p) ω
ω^-mono            (≤-ℓ n p) = ≤-ℓ n (ω^-mono p)
ω^-mono            (≤-L p)   = ≤-L (λ n → ω^-mono (p n))

\end{code}

The numerals are below `ω`, hence `ω^ ι[ m ] ≤ ω^ ω = tower 1`: every
*finite* `ω`-power is below the first tower level. This is the absorption
that keeps first-order magnitudes (finite) from escaping `ω^ω`.

\begin{code}

ι[_]≤ω : (m : ℕ) → ι[ m ] ≤ ω
ι[ m ]≤ω = ≤-L-upper-bound ι[_] m

finite-power-≤-ω^ω : (m : ℕ) → ω^ ι[ m ] ≤ tower 1
finite-power-≤-ω^ω m = ω^-mono ι[ m ]≤ω

\end{code}

Exponentiation is inflationary: `a ≤ ω^ a`. The successor step uses that a
single `ω`-power dominates its predecessor doubled
(`S (ω^ a) ≤ ω^ a ⊕ ω^ a ≤ ω^ a ⊗ ω`), routing around the
successor-of-limit case that the naive proof would hit.

\begin{code}

S-ω^-step : (a : 𝓑) → S (ω^ a) ≤ (ω^ a ⊗ ω)
S-ω^-step a = ≤-trans h1 h2
 where
  h1 : S (ω^ a) ≤ (ω^ a ⊕ ω^ a)
  h1 = ⊕-mono-right (ω^ a) (one-≤-ω^ a)

  eq2 : (ω^ a ⊗ ι[ 2 ]) ＝ (ω^ a ⊕ ω^ a)
  eq2 = ap (_⊕ ω^ a) (Z-left-unit (ω^ a))

  h2 : (ω^ a ⊕ ω^ a) ≤ (ω^ a ⊗ ω)
  h2 = transport (_≤ (ω^ a ⊗ ω)) eq2
                 (≤-L-upper-bound (λ n → ω^ a ⊗ ι[ n ]) 2)

≤-ω^ : (a : 𝓑) → a ≤ ω^ a
≤-ω^ Z     = ≤-Z
≤-ω^ (S a) = ≤-trans (≤-S (≤-ω^ a)) (S-ω^-step a)
≤-ω^ (L f) = ≤-L-mono (λ n → ≤-ω^ (f n))

\end{code}

`ω` is `ω^ 1` (one times `ω`), and strictly below `ω^ ω`: the first place
the tower genuinely climbs.

\begin{code}

one-⊗-ι : (n : ℕ) → (S Z ⊗ ι[ n ]) ＝ ι[ n ]
one-⊗-ι zero     = refl
one-⊗-ι (succ n) = ap (_⊕ S Z) (one-⊗-ι n)

ω^-ι1 : ω^ ι[ 1 ] ＝ ω
ω^-ι1 = ap L (dfunext fe one-⊗-ι)

ω<ω^ω : S ω ≤ ω^ ω
ω<ω^ω = transport (λ z → S z ≤ ω^ ω) ω^-ι1
                  (≤-trans (S-ω^-step ι[ 1 ])
                           (ω^-mono (≤-L-upper-bound ι[_] 2)))

\end{code}

The multiplication absorption that the orbit engine's output needs: the
first-order recursor bound `ω^ω ⊗ ω` is below the second tower level.

\begin{code}

ω^ω⊗ω-≤-tower2 : (ω^ ω ⊗ ω) ≤ tower 2
ω^ω⊗ω-≤-tower2 = ω^-mono ω<ω^ω

\end{code}

The tower is *strictly* increasing — `tower n < tower (succ n)` — and hence
every level is `< ε₀`. The successor-of-limit obstruction is dissolved by a
descent: strictness at `ω^ b` reduces, via `S-ω^-step` and `ω^-mono`, to
strictness at `b`, bottoming out at the proved base `ω < ω^ ω`.

\begin{code}

tower-strict : (n : ℕ) → S (tower n) ≤ ω^ (tower n)
tower-strict zero     = ω<ω^ω
tower-strict (succ m) = ≤-trans (S-ω^-step (tower m))
                                (ω^-mono (tower-strict m))

tower-<-ε₀ : (n : ℕ) → tower n < ε₀
tower-<-ε₀ n = ≤-ℓ (succ n) (tower-strict n)

\end{code}

The strict bound the orbit engine's first-order output needs:
`ω^ω ⊗ ω < ε₀`.

\begin{code}

ω^ω⊗ω-<-ε₀ : (ω^ ω ⊗ ω) < ε₀
ω^ω⊗ω-<-ε₀ = ≤-trans (≤-S ω^ω⊗ω-≤-tower2) (tower-<-ε₀ 2)

\end{code}

The additive `< ε₀` closure, to fold the engine's output
`(height x ⊕ ω^ω ⊗ ω) ⊕ height n` into a single `< ε₀` once the heights of
the subterms are `< ε₀`. The towers are closed under doubling
(`tower-double`, from `ω^ a ⊕ ω^ a ≤ ω^ a ⊗ ω`), and monotone in their
ℕ-index; combining two ordinals below ε₀ pushes them to a common tower
level and doubles.

\begin{code}

ω^-double : (a : 𝓑) → (ω^ a ⊕ ω^ a) ≤ (ω^ a ⊗ ω)
ω^-double a =
 transport (_≤ (ω^ a ⊗ ω)) (ap (_⊕ ω^ a) (Z-left-unit (ω^ a)))
           (≤-L-upper-bound (λ n → ω^ a ⊗ ι[ n ]) 2)

tower-mono-step : (n : ℕ) → tower n ≤ tower (succ n)
tower-mono-step n = ≤-trans (S-increasing (tower n)) (tower-strict n)

tower-double : (n : ℕ) → (tower n ⊕ tower n) ≤ tower (succ n)
tower-double zero =
 transport (λ z → (z ⊕ z) ≤ tower 1) ω^-ι1
           (≤-trans (ω^-double ι[ 1 ]) (ω^-mono (≤-L-upper-bound ι[_] 2)))
tower-double (succ m) =
 ≤-trans (ω^-double (tower m)) (ω^-mono (tower-strict m))

\end{code}

A little `ℕ`-max with its order, to reach a common tower level.

\begin{code}

maxℕ : ℕ → ℕ → ℕ
maxℕ zero     n        = n
maxℕ (succ m) zero     = succ m
maxℕ (succ m) (succ n) = succ (maxℕ m n)

_≤ℕ_ : ℕ → ℕ → 𝓤₀ ̇
zero   ≤ℕ n      = 𝟙
succ m ≤ℕ zero   = 𝟘
succ m ≤ℕ succ n = m ≤ℕ n

≤ℕ-refl : (n : ℕ) → n ≤ℕ n
≤ℕ-refl zero     = ⋆
≤ℕ-refl (succ n) = ≤ℕ-refl n

≤ℕ-maxL : (m n : ℕ) → m ≤ℕ maxℕ m n
≤ℕ-maxL zero     n        = ⋆
≤ℕ-maxL (succ m) zero     = ≤ℕ-refl (succ m)
≤ℕ-maxL (succ m) (succ n) = ≤ℕ-maxL m n

≤ℕ-maxR : (m n : ℕ) → n ≤ℕ maxℕ m n
≤ℕ-maxR zero     n        = ≤ℕ-refl n
≤ℕ-maxR (succ m) zero     = ⋆
≤ℕ-maxR (succ m) (succ n) = ≤ℕ-maxR m n

tower-mono-ℕ : (m n : ℕ) → m ≤ℕ n → tower m ≤ tower n
tower-mono-ℕ zero     zero     p = ≤-refl (tower 0)
tower-mono-ℕ zero     (succ n) p = ≤-trans (tower-mono-ℕ zero n ⋆) (tower-mono-step n)
tower-mono-ℕ (succ m) zero     p = 𝟘-elim p
tower-mono-ℕ (succ m) (succ n) p = ω^-mono (tower-mono-ℕ m n p)

\end{code}

The additive closure: `a < ε₀` and `b < ε₀` give `a ⊕ b < ε₀`. Inverting
`a < ε₀` to a tower level is the single `≤-ℓ` constructor (the only way a
successor sits below the limit `ε₀`), so it is a clean pattern match.

\begin{code}

⊕-<-ε₀ : (a b : 𝓑) → a < ε₀ → b < ε₀ → (a ⊕ b) < ε₀
⊕-<-ε₀ a b (≤-ℓ j qa) (≤-ℓ j′ qb) =
 ≤-trans (≤-S ab-≤) (tower-<-ε₀ (succ Jm))
 where
  Jm : ℕ
  Jm = maxℕ j j′

  a≤Jm : a ≤ tower Jm
  a≤Jm = ≤-trans (S-increasing a) (≤-trans qa (tower-mono-ℕ j Jm (≤ℕ-maxL j j′)))

  b≤Jm : b ≤ tower Jm
  b≤Jm = ≤-trans (S-increasing b) (≤-trans qb (tower-mono-ℕ j′ Jm (≤ℕ-maxR j j′)))

  ab-≤ : (a ⊕ b) ≤ tower (succ Jm)
  ab-≤ = ≤-trans (≤-trans (⊕-mono-left a≤Jm b) (⊕-mono-right (tower Jm) b≤Jm))
                 (tower-double Jm)

\end{code}

Two exponentiation closures of `ε₀`, needed once the tower-step exponent is
allowed to be a genuine ordinal rather than a numeral (the higher-type
mechanism, `Bridge`). `ε₀` is closed under successor and — the substantial
one — under `ω^_`: if `a < ε₀`, some tower level `tower n` dominates `a`, so
`ω^ a ≤ ω^ (tower n) = tower (succ n) < ε₀`. Both invert `a < ε₀` by the
single `≤-ℓ` constructor, as with `⊕-<-ε₀`.

\begin{code}

S-<-ε₀ : (a : 𝓑) → a < ε₀ → S a < ε₀
S-<-ε₀ a (≤-ℓ n q) = ≤-trans (≤-S q) (tower-<-ε₀ n)

ω^-<-ε₀ : (a : 𝓑) → a < ε₀ → ω^ a < ε₀
ω^-<-ε₀ a (≤-ℓ n q) =
 ≤-trans (≤-S (ω^-mono (≤-trans (S-increasing a) q))) (tower-<-ε₀ (succ n))

\end{code}

So sub-development (I) is complete: every code the first-order orbit engine
produces from sub-`ε₀` ingredients is itself `< ε₀`, and `ε₀` is moreover
closed under the successor and `ω`-exponentiation the tower climb needs.
