The bump family: the per-storey multiplier arithmetic of the Howard tower.

In the level-indexed tracking design (`dialogue-tree-height-howard-tower.md`,
following `MultHereditaryG`), a function argument `h` contributes to a
consumer's zone bound in two ways: its additive part enters the zone like a
ground argument, and its multiplier `M_h` enters through a *multiplier map*.
The maps that arise are exactly the finite iterates of the recursor's
raise, `bump M = ω^ ((ω ⊗ M) ⊗ ω)` — the multiplier of
`MultHereditaryFAff.AffBounded-orbit` and `MultHereditaryG.Tracked-dOrbit` —
so the whole class of multiplier maps a first-order term generates is the
ℕ-indexed family `bumpk k`, and the tower's storeys need only this family
plus its absorption laws:

* `bumpk` preserves `ValidMult` and is monotone in both arguments
  (`bumpk-valid`, `bumpk-mono`, `bumpk-≤-succ`, inflationary `≤-bump`);
* **products absorb into one extra bump** (`⊗-≤-bump`,
  `bumpk-⊗-absorb`): `X ⊗ X ≤ bump X`, hence using an argument's
  multiplier any finite number of times, or combining two arguments'
  multipliers (`⊕`-joined), costs one bump;
* **the recursor's raise is a bump by definition** (`AffBounded-orbit`'s
  multiplier `ω^ ((ω ⊗ M) ⊗ ω)` *is* `bump M`), so nested recursion moves
  `k ↦ k + 1`;
* everything stays `< ε₀` (`bumpk-<-ε₀`).

Pure ordinal arithmetic, no new ideas — the load-bearing inequalities are
`≤-ω^` (inflationarity) and the exponent homomorphism `ω^⊗`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.BrouwerOrdinals.MultBump
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import Claude.BrouwerOrdinals.Order fe
open import Claude.BrouwerOrdinals.Orbit fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ω^_ ; ω^-mono ; ≤-ω^ ; one-≤-ω^ ;
        ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right ;
        ⊕-increasing-right ; ω^-<-ε₀ ; tower-<-ε₀)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊕-increasing-left)
open import Claude.BrouwerOrdinals.OmegaPoly fe
 using (⊗-<-ε₀ ; ω^⊗)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (x-≤-x⊗ ; y-≤-⊗)
open import Claude.BrouwerOrdinals.MultAffine fe using (ω-pos)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; ω-valid ; validMult-⊗ ; validMult-orbit)

\end{code}

The bump and its iterates.

\begin{code}

bump : 𝓑 → 𝓑
bump M = ω^ ((ω ⊗ M) ⊗ ω)

bumpk : ℕ → 𝓑 → 𝓑
bumpk zero     M = M
bumpk (succ k) M = bump (bumpk k M)

\end{code}

Validity, monotonicity, inflationarity, and the `< ε₀` bound.

\begin{code}

bump-valid : {M : 𝓑} → ValidMult M → ValidMult (bump M)
bump-valid vM = validMult-orbit (validMult-⊗ ω-valid vM)

bumpk-valid : (k : ℕ) {M : 𝓑} → ValidMult M → ValidMult (bumpk k M)
bumpk-valid zero     vM = vM
bumpk-valid (succ k) vM = bump-valid (bumpk-valid k vM)

bump-mono : {M N : 𝓑} → M ≤ N → bump M ≤ bump N
bump-mono h = ω^-mono (⊗-mono-left (⊗-mono-right ω h) ω)

bumpk-mono : (k : ℕ) {M N : 𝓑} → M ≤ N → bumpk k M ≤ bumpk k N
bumpk-mono zero     h = h
bumpk-mono (succ k) h = bump-mono (bumpk-mono k h)

≤-bump : (M : 𝓑) → M ≤ bump M
≤-bump M = ≤-trans (≤-ω^ M)
            (ω^-mono (≤-trans (y-≤-⊗ ω M ω-pos)
                              (x-≤-x⊗ (ω ⊗ M) ω ω-pos)))

bumpk-≤-succ : (k : ℕ) (M : 𝓑) → bumpk k M ≤ bumpk (succ k) M
bumpk-≤-succ k M = ≤-bump (bumpk k M)

bump-<-ε₀ : {M : 𝓑} → M < ε₀ → bump M < ε₀
bump-<-ε₀ {M} p =
 ω^-<-ε₀ ((ω ⊗ M) ⊗ ω)
         (⊗-<-ε₀ (ω ⊗ M) ω (⊗-<-ε₀ ω M (tower-<-ε₀ 0) p) (tower-<-ε₀ 0))

bumpk-<-ε₀ : (k : ℕ) {M : 𝓑} → M < ε₀ → bumpk k M < ε₀
bumpk-<-ε₀ zero     p = p
bumpk-<-ε₀ (succ k) p = bump-<-ε₀ (bumpk-<-ε₀ k p)

\end{code}

Product absorption: a square is dominated by one bump, via inflationarity
and the exponent homomorphism `ω^ a ⊗ ω^ b ＝ ω^ (a ⊕ b)`.

\begin{code}

⊗-≤-bump : (X : 𝓑) → (X ⊗ X) ≤ bump X
⊗-≤-bump X =
 ≤-trans (⊗-mono-left (≤-ω^ X) (X))
  (≤-trans (⊗-mono-right (ω^ X) (≤-ω^ X))
    (transport (λ z → z ≤ bump X) ((ω^⊗ X X) ⁻¹) expo))
 where
  X⊕X-≤ : (X ⊕ X) ≤ ((ω ⊗ X) ⊗ ω)
  X⊕X-≤ = ≤-trans (⊕-mono-left (⊕-increasing-left Z X) X)
           (≤-trans (⊗-mono-right X (≤-L-upper-bound ι[_] 2))
                    (⊗-mono-left (y-≤-⊗ ω X ω-pos) ω))

  expo : ω^ (X ⊕ X) ≤ bump X
  expo = ω^-mono X⊕X-≤

\end{code}

Combining two multipliers: their `⊗`-product is absorbed by one bump of
their `⊕`-join — the law that lets a consumer's zone use several function
arguments' multipliers (and each of them repeatedly) at the cost of a
single storey.

\begin{code}

bumpk-⊗-absorb : (k : ℕ) (M N : 𝓑)
               → (bumpk k M ⊗ bumpk k N) ≤ bumpk (succ k) (M ⊕ N)
bumpk-⊗-absorb k M N =
 ≤-trans (⊗-mono-left (bumpk-mono k (⊕-increasing-right M N)) (bumpk k N))
  (≤-trans (⊗-mono-right (bumpk k (M ⊕ N))
                         (bumpk-mono k (⊕-increasing-left M N)))
           (⊗-≤-bump (bumpk k (M ⊕ N))))

\end{code}

The recursor's raise is a bump, definitionally: `AffBounded-orbit` and
`Tracked-dOrbit` raise a multiplier `M` to `ω^ ((ω ⊗ M) ⊗ ω) = bump M`.
So in the storey accounting, one recursor nesting is `k ↦ succ k`.

\begin{code}

orbit-raise-is-bump : (M : 𝓑) → ω^ ((ω ⊗ M) ⊗ ω) ＝ bump M
orbit-raise-is-bump M = refl

\end{code}
