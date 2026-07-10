The recursor height bound, conditional on an orbit bound.

The residual lemma (the orbit bound: for each System T iteration there is a
bound `b`, an ordinal `< ε₀`, on the *orbit of heights* `k ↦ height (fᵏ x)`)
is the genuinely open, dialogue-specific content.

(Framing corrected — Howard *is* the lever, not an obstacle. An earlier note
here claimed this is "not a corollary of Howard's 1970 ordinal assignment,
because dialogue height is independent of value magnitude". That conflated
two things Howard controls. Howard bounds not only a term's *value* but the
*ordinal rank* of its computation's well-founded structure — and the
dialogue height is exactly such a rank (it is not a value, and not even the
query-count: an ω-branching well-founded tree with every branch finite can
have rank `ω²`, `ω^ω`, …). The rank-`ω`/magnitude-`0` witness shows height is
independent of *value*, but Howard's ordinal `o(t)` is a structural-
complexity ordinal that *dominates* such ranks: on that witness
`o(λα. iter α b (α 0)) ≥ ω`, since `o` sees the iteration, not the value. So
the orbit bound is the dialogue-side instance of Howard's `|System T| = ε₀`,
decomposed as **(A)** the magnitude/value orbit grows at a rate `< ε₀` —
classical Howard, citable — plus **(B)** the dialogue-native bridge
"height-increment `≤ ω^magnitude`", height riding on (A) via the Count Lemma.
(B) is the residual; (A) is Howard. See `…TwoComponent` for the structure.)

What this module does is honest and modest: it takes the orbit bound as an
explicit **hypothesis** and *proves* that the height of the ground iteration
`iter' f x n = kleisli-extension (iter f x) n` is then `≤ b ⊕ height n`. So
this is the machine-checked content of the *implication* "orbit bound ⟹
recursor height bound" — the assumption is a function argument, never a
`postulate`. It does **not** establish the conjecture, because the
hypothesis itself is unproved.

The proof rides entirely on the machine-checked engine: the recursor
identity `height-iter'` and the operator `H` with the constructive
Brouwer-code order.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.Conditional
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Operator fe

\end{code}

If a leaf valuation `v` is pointwise bounded by `b`, then the operator `H`
maps it below `b ⊕ height d` for every tree `d`. (This is the operator-level
form of the grafting bound, with the *uniform* bound `b` standing in for the
valuation — exactly the move the Count Lemma justifies when the count is
unbounded.)

\begin{code}

H-bounded : (v : ℕ → 𝓑) (b : 𝓑)
          → ((k : ℕ) → v k ≤ b)
          → (d : B ℕ)
          → H v d ≤ (b ⊕ height d)
H-bounded v b hyp (η k)   = hyp k
H-bounded v b hyp (β φ i) =
 ≤-L-mono (λ j → ≤-S (H-bounded v b hyp (φ j)))

\end{code}

The recursor bound from an orbit bound. Given a bound `b` for `k ↦ height
(iter f x k)` — an explicit hypothesis, the residual open lemma (the
dialogue-side instance of Howard's `|System T| = ε₀`; see the corrected note
above and `…TwoComponent` for the (A)+(B) decomposition) — the ground
iteration has height `≤ b ⊕ height n`. Combined with `ε₀`-closure
(`b < ε₀` ⟹ `b ⊕ height n < ε₀`), this is the recursor case of the conjecture
*conditional on the orbit bound*.

\begin{code}

height-iter-≤-orbit-bound
 : (f : B ℕ → B ℕ) (x : B ℕ) (b : 𝓑)
 → ((k : ℕ) → height (iter f x k) ≤ b)          -- DML's orbit bound, as an assumption
 → (n : B ℕ)
 → height (kleisli-extension (iter f x) n) ≤ (b ⊕ height n)
height-iter-≤-orbit-bound f x b hyp n =
 transport (_≤ (b ⊕ height n))
           ((height-iter' f x n) ⁻¹)
           (H-bounded (λ k → height (iter f x k)) b hyp n)

\end{code}
