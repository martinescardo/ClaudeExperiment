The syntactic order and addition on Brouwer ordinal codes.

This is the base of the `BrouwerOrdinals` development: the constructive
order `_≤_` on Brouwer codes (`Ordinals.BrouwerCodes`), for which the
successor is monotone *by construction* (no excluded middle), and ordinal
addition `_⊕_`. Everything here is pure ordinal arithmetic — it makes no
reference to dialogue trees, System T, or the dialogue-tree-height
conjecture; those consume this module (e.g.
`Claude.DialogueTreeHeight.Constructive`, which adds the height
function on top and re-exports this order).

The module is parameterized by function extensionality only for uniformity
with the rest of the library; the definitions here do not use it.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.BrouwerOrdinals.Order
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)

\end{code}

The syntactic order on Brouwer codes. The constructors say: `Z` is least;
the successor is monotone; `L f` is above each `f n` (the cocone `≤-ℓ`);
and `L f` is below any upper bound of the `f n` (the limiting property
`≤-L`). So `L f` is the least upper bound of the family `f`, and the
successor is monotone with no side condition.

\begin{code}

infix 4 _≤_

data _≤_ : 𝓑 → 𝓑 → 𝓤₀ ̇ where
 ≤-Z : {b : 𝓑} → Z ≤ b
 ≤-S : {a b : 𝓑} → a ≤ b → S a ≤ S b
 ≤-ℓ : {a : 𝓑} {f : ℕ → 𝓑} (n : ℕ) → a ≤ f n → a ≤ L f
 ≤-L : {f : ℕ → 𝓑} {b : 𝓑} → ((n : ℕ) → f n ≤ b) → L f ≤ b

≤-refl : (a : 𝓑) → a ≤ a
≤-refl Z     = ≤-Z
≤-refl (S a) = ≤-S (≤-refl a)
≤-refl (L f) = ≤-L (λ n → ≤-ℓ n (≤-refl (f n)))

\end{code}

Transitivity. The recursion is lexicographic: when the left proof is a
limit `≤-L p` we recurse on the strictly smaller `p n` (keeping the right
proof fixed); otherwise we recurse on a strictly smaller right proof.

\begin{code}

≤-trans : {a b c : 𝓑} → a ≤ b → b ≤ c → a ≤ c
≤-trans ≤-Z       _         = ≤-Z
≤-trans (≤-L p)   q         = ≤-L (λ n → ≤-trans (p n) q)
≤-trans (≤-S p)   (≤-S q)   = ≤-S (≤-trans p q)
≤-trans (≤-S p)   (≤-ℓ n q) = ≤-ℓ n (≤-trans (≤-S p) q)
≤-trans (≤-ℓ n p) (≤-ℓ m q) = ≤-ℓ m (≤-trans (≤-ℓ n p) q)
≤-trans (≤-ℓ n p) (≤-L q)   = ≤-trans p (q n)

\end{code}

Two derived facts: the limit is monotone in its family, and the cocone
into a limit (`f n ≤ L f`) holds.

\begin{code}

≤-L-mono : {f g : ℕ → 𝓑} → ((n : ℕ) → f n ≤ g n) → L f ≤ L g
≤-L-mono p = ≤-L (λ n → ≤-ℓ n (p n))

≤-L-upper-bound : (f : ℕ → 𝓑) (n : ℕ) → f n ≤ L f
≤-L-upper-bound f n = ≤-ℓ n (≤-refl (f n))

\end{code}

Addition of Brouwer codes, by recursion on the right argument (ordinal
addition). Crucially `a ⊕ S b = S (a ⊕ b)`, so adding on the left
commutes with successors and limits definitionally.

\begin{code}

infixl 6 _⊕_

_⊕_ : 𝓑 → 𝓑 → 𝓑
a ⊕ Z   = a
a ⊕ S b = S (a ⊕ b)
a ⊕ L f = L (λ n → a ⊕ f n)

\end{code}
