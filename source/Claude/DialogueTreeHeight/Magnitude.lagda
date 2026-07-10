Oracle-relative magnitude for dialogue trees (constructive).

This is the machine-checked **magnitude** half of the two-component
analysis (`dialogue-tree-height-two-component.md` §2,
`…-howard-build.md` §1 `R_ι` and Lemma R1). Height alone is blind to
iteration counts, which are leaf *values*; the missing component is the
*magnitude* — a bound on the values a tree produces. Because the oracle can
answer with arbitrarily large numbers, a raw bound on leaf values is `∞`
whenever the oracle is used. The right notion is therefore **relative to a
bound on the oracle**:

  `mag-≤ V x` :⟺ for every oracle `α` bounded by `b`, the value
                `dialogue x α` is `≤ V b`.

`V : ℕ → ℕ` is the *magnitude function* (`V b` bounds values under oracles
`≤ b`). We prove the propagation laws — the machine-checked form of
"magnitude comes from the oracle, and only the oracle":

* a leaf has constant magnitude (`mag-η`);
* `succ` increments it (`mag-succ'`);
* **`generic` resets it to the identity `λ b → b`, regardless of the input
  (`mag-generic`)** — the oracle is the sole source of magnitude, and it
  caps the value at the current oracle bound;
* grafting (`kleisli-extension`) composes magnitudes through the count, and
  in doing so realises **Lemma R1 (the count bound)**: the iteration count
  `dialogue n α` performed at oracle `α ≤ b` is itself `≤ V b`.

This is exactly the component the height-only majorant could not see, and it
is what the orbit engine (`DialogueTreeHeight.Orbit`) consumes to fix the
per-step increment. Self-contained over `Dialogue`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.Magnitude
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import EffectfulForcing.MFPSAndVariations.Continuity using (Baire)
open import EffectfulForcing.MFPSAndVariations.Dialogue

\end{code}

A self-contained order on the naturals (avoiding clashes with the
Brouwer-code order elsewhere), with the facts we need.

\begin{code}

_≤ℕ_ : ℕ → ℕ → 𝓤₀ ̇
zero   ≤ℕ n      = 𝟙
succ m ≤ℕ zero   = 𝟘
succ m ≤ℕ succ n = m ≤ℕ n

≤ℕ-refl : (n : ℕ) → n ≤ℕ n
≤ℕ-refl zero     = ⋆
≤ℕ-refl (succ n) = ≤ℕ-refl n

≤ℕ-trans : (l m n : ℕ) → l ≤ℕ m → m ≤ℕ n → l ≤ℕ n
≤ℕ-trans zero     m        n        p q = ⋆
≤ℕ-trans (succ l) zero     n        p q = 𝟘-elim p
≤ℕ-trans (succ l) (succ m) zero     p q = 𝟘-elim q
≤ℕ-trans (succ l) (succ m) (succ n) p q = ≤ℕ-trans l m n p q

\end{code}

A bound on the oracle: `α ≤[ b ]` means every value `α i` is `≤ b`.

\begin{code}

_≤[_] : Baire → ℕ → 𝓤₀ ̇
α ≤[ b ] = (i : ℕ) → α i ≤ℕ b

\end{code}

The magnitude bound. `V` bounds the values of `x` under oracles `≤ b`.

\begin{code}

mag-≤ : (ℕ → ℕ) → B ℕ → 𝓤₀ ̇
mag-≤ V x = (b : ℕ) (α : Baire) → α ≤[ b ] → dialogue x α ≤ℕ V b

\end{code}

A leaf `η n` has constant magnitude `n`.

\begin{code}

mag-η : (n : ℕ) → mag-≤ (λ _ → n) (η n)
mag-η n b α _ = ≤ℕ-refl n

\end{code}

`succ' = B-functor succ` increments the magnitude function by one. The value
identity `dialogue (B-functor succ x) α ＝ succ (dialogue x α)` is
naturality of `decode`.

\begin{code}

mag-succ' : (V : ℕ → ℕ) (x : B ℕ)
          → mag-≤ V x
          → mag-≤ (λ b → succ (V b)) (B-functor succ x)
mag-succ' V x m b α h =
 transport (_≤ℕ succ (V b))
           (decode-α-is-natural succ x α)
           (m b α h)

\end{code}

The oracle resets magnitude to the identity, *independently of the input's
magnitude*: `dialogue (generic x) α ＝ α (dialogue x α)`, and any oracle
value is `≤ b`. This is the unique source of magnitude, and it never
amplifies beyond the current oracle bound.

\begin{code}

mag-generic : (x : B ℕ) → mag-≤ (λ b → b) (generic x)
mag-generic x b α h =
 transport (_≤ℕ b)
           (generic-diagram α x)
           (h (dialogue x α))

\end{code}

Grafting composes magnitudes through the count. The result value is the
value of `g k` at the count `k = dialogue n α`, which is `≤ V b` (this is
**Lemma R1**, the count bound). Given a magnitude `W k` for each graft `g k`,
monotone in the count, the result magnitude is `λ b → W (V b) b`.

\begin{code}

mag-kleisli
 : (g : ℕ → B ℕ) (W : ℕ → ℕ → ℕ) (V : ℕ → ℕ) (n : B ℕ)
 → ((k : ℕ) → mag-≤ (W k) (g k))
 → ((k k′ : ℕ) → k ≤ℕ k′ → (b : ℕ) → W k b ≤ℕ W k′ b)
 → mag-≤ V n
 → mag-≤ (λ b → W (V b) b) (kleisli-extension g n)
mag-kleisli g W V n gm W-mono nm b α h =
 transport (_≤ℕ W (V b) b)
           (decode-kleisli-extension g n α)
           (≤ℕ-trans (dialogue (g c) α) (W c b) (W (V b) b)
                     (gm c b α h)
                     (W-mono c (V b) count-bound b))
 where
  c : ℕ
  c = dialogue n α

  count-bound : c ≤ℕ V b      -- Lemma R1: the count is bounded by the magnitude
  count-bound = nm b α h

\end{code}

The count bound on its own, named for reuse: in `kleisli-extension g n` the
iteration count `dialogue n α` at any oracle `α ≤ b` is `≤ V b`.

\begin{code}

count-bound-R1 : (V : ℕ → ℕ) (n : B ℕ)
               → mag-≤ V n
               → (b : ℕ) (α : Baire) → α ≤[ b ] → dialogue n α ≤ℕ V b
count-bound-R1 V n nm = nm

\end{code}
