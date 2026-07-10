Ordinal multiplication, `ω`, and the fixed-increment orbit engine.

Pure Brouwer-ordinal arithmetic building on `Claude.BrouwerOrdinals.Order`: the
numeral embedding `ι[_]`, the first limit `ω`, ordinal multiplication `_⊗_`,
left-monotonicity and associativity of `_⊕_`, and the **orbit engine** — if a
sequence `a : ℕ → 𝓑` grows by at most a fixed code `c` per step
(`a (succ k) ≤ a k ⊕ c`), then `L a ≤ a 0 ⊕ (c ⊗ ω)` (one factor of `ω`, the
single `ω` that a depth-independent increment permits).

This module makes no reference to dialogue trees or System T. The
dialogue-tree-height reading of the orbit engine — that a per-step *height*
increment yields an iteration bound — lives in
`Claude.DialogueTreeHeight.Orbit`, which consumes and re-exports
this module.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.BrouwerOrdinals.Orbit
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import Claude.BrouwerOrdinals.Order fe

\end{code}

The numeral embedding, `ω` as the supremum of the numerals, and ordinal
multiplication (recursion on the right argument, matching `⊕`).

\begin{code}

ι[_] : ℕ → 𝓑
ι[ zero ]   = Z
ι[ succ n ] = S ι[ n ]

ω : 𝓑
ω = L ι[_]

infixl 7 _⊗_

_⊗_ : 𝓑 → 𝓑 → 𝓑
a ⊗ Z   = Z
a ⊗ S b = (a ⊗ b) ⊕ a
a ⊗ L f = L (λ n → a ⊗ f n)

\end{code}

Two facts about `⊕`: monotonicity in the left argument, and associativity.
(Associativity is the only place we use function extensionality, for the
limit case.)

\begin{code}

⊕-mono-left : {a a′ : 𝓑} → a ≤ a′ → (c : 𝓑) → (a ⊕ c) ≤ (a′ ⊕ c)
⊕-mono-left p Z     = p
⊕-mono-left p (S c) = ≤-S (⊕-mono-left p c)
⊕-mono-left p (L f) = ≤-L-mono (λ n → ⊕-mono-left p (f n))

⊕-assoc : (a b c : 𝓑) → ((a ⊕ b) ⊕ c) ＝ (a ⊕ (b ⊕ c))
⊕-assoc a b Z     = refl
⊕-assoc a b (S c) = ap S (⊕-assoc a b c)
⊕-assoc a b (L f) = ap L (dfunext fe (λ n → ⊕-assoc a b (f n)))

\end{code}

The orbit engine. Fix a sequence `a : ℕ → 𝓑` and a fixed per-step increment
`c`, with `step` saying each step grows the sequence by at most `c`.

\begin{code}

module _ (a : ℕ → 𝓑) (c : 𝓑)
         (step : (k : ℕ) → a (succ k) ≤ (a k ⊕ c))
       where

\end{code}

The `k`-th orbit point is bounded by the start plus `c` taken `k` times.
The successor step is where linearity bites: the increment is the *same* `c`
regardless of how large `a k` already is, so the bound accumulates by
ordinary multiplication, not by feeding the depth back into itself.

\begin{code}

 orbit-≤ : (k : ℕ) → a k ≤ (a 0 ⊕ (c ⊗ ι[ k ]))
 orbit-≤ zero     = ≤-refl (a 0)
 orbit-≤ (succ k) =
  transport (λ - → a (succ k) ≤ -)
            (⊕-assoc (a 0) (c ⊗ ι[ k ]) c)
            (≤-trans (step k) (⊕-mono-left (orbit-≤ k) c))

\end{code}

Hence the orbit *supremum* `L a` is bounded by `a 0 ⊕ (c ⊗ ω)` — one extra
factor of `ω`, the single `ω` that linearity permits per iteration.

\begin{code}

 orbit-sup-≤ : L a ≤ (a 0 ⊕ (c ⊗ ω))
 orbit-sup-≤ = ≤-L-mono orbit-≤

\end{code}

The uniform bound: every orbit point is below the single code
`a 0 ⊕ (c ⊗ ω)`.

\begin{code}

 orbit-uniform : (k : ℕ) → a k ≤ (a 0 ⊕ (c ⊗ ω))
 orbit-uniform k = ≤-trans (≤-L-upper-bound a k) orbit-sup-≤

\end{code}
