The limit-multiplier affine orbit (constructive) — iterating `b ↦ (b ⊕ c) ⊗ M`.

The finite-multiplier affine class `Aff` (`AffineClosure`) iterates because of
`Affine.affine-fold` — `b ⊗ ι[m] ⊕ d ≤ (b ⊕ d) ⊗ ι[m]` — which lets the orbit
constant be pulled outside the multiplier. That fold is provably **false for a
limit multiplier** (`b ⊗ ω ⊕ d ≤ (b ⊕ d) ⊗ ω` fails: `1 ⊗ ω ⊕ 1 = ω + 1 >
ω = 2 ⊗ ω`). This is exactly why the start-varying recursor — whose majorant is
`ω`-affine, `L (λ k → iter ρ a k) ≤ (a ⊕ d ⊗ ω) ⊗ ω` — "could not iterate", and
it is where the type-level tower lives.

This module iterates a limit-multiplier affine body **without** `affine-fold`.
The body is `mbody c b = (b ⊕ c) ⊗ M` for any multiplier `M` that is positive
and *absorbs doubling* — `ι[2] ⊗ M ≤ M` (true for every principal limit:
`ω`, `ω ⊗ 2`, `ω^ω`, …). Instead of pulling `c` out of the multiplier, we push
`⊗ M` *inward*: the single arithmetic fact

  `crux : c ≤ Y → (Y ⊕ c) ⊗ M ≤ Y ⊗ M`

(a `c` below `Y` is absorbed on iterating, because `Y ⊕ c ≤ Y ⊕ Y = Y ⊗ ι[2]`
and `ι[2] ⊗ M ≤ M`). With it the orbit telescopes against the powers `Mᵏ`
(`MultOrbit.pw`):

  `iter (mbody c) a k ≤ (a ⊕ c) ⊗ Mᵏ`,

whose supremum is `(a ⊕ c) ⊗ ω^(M ⊗ ω) < ε₀` (via `MultOrbit.pw-sup-≤`). So a
*limit*-multiplier affine map iterates and its orbit is `< ε₀`, with the
multiplier anywhere below `ε₀` — the first `ω`-multiplier affine orbit bounded,
the honest first crack in the multiplier wall the finite-`Aff` class stopped at.

(Scope, honestly: this closes the limit-multiplier affine *body* — one level.
The full start-varying recursor diagonal has this shape only up to lower-order
`⊕ γ a` terms, and *nesting* it climbs the tower further; those remain the open
core. What is new here is that limit-multiplier iteration is no longer blocked
by the `affine-fold` failure.)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.BrouwerOrdinals.MultAffine
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import Claude.BrouwerOrdinals.Order fe
open import Claude.BrouwerOrdinals.Orbit fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (ω^_ ; _<_ ; ε₀ ; ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right ;
        Z-left-unit ; ⊕-increasing-right ; ⊕-<-ε₀ ; tower-<-ε₀ ;
        one-≤-ω^ ; ω^-mono ; ω^-ι1 ; ω^-<-ε₀)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊗-assoc ; _·ℕ_ ; ι-*-homo ; ⊕-increasing-left ; affine-orbit-≤)
open import Claude.BrouwerOrdinals.OmegaPoly fe
 using (⊗-<-ε₀ ; ω^⊗ ; S⊕≤S)
open import Claude.BrouwerOrdinals.MultOrbit fe
 using (pw ; pw-sup-≤ ; pw-sup-<-ε₀)

\end{code}

A finite multiple of `ω` collapses to `ω`: `ι[n] ⊗ ω ≤ ω` (each
`ι[n] ⊗ ι[j] = ι[n ·ℕ j]` is a numeral, dominated by `ω = L ι[_]` at its own
index). In particular `ι[2] ⊗ ω ≤ ω`, the doubling-absorption for `M = ω`.

\begin{code}

ιn⊗ω-≤-ω : (n : ℕ) → (ι[ n ] ⊗ ω) ≤ ω
ιn⊗ω-≤-ω n =
 ≤-L (λ j → transport (_≤ ω) ((ι-*-homo n j) ⁻¹)
                      (≤-L-upper-bound ι[_] (n ·ℕ j)))

\end{code}

Domination of orbits: if `f ≤ g` pointwise and `g` is monotone, every `f`-orbit
point is below the corresponding `g`-orbit point.

\begin{code}

iter-dominate : {f g : 𝓑 → 𝓑}
              → ((b : 𝓑) → f b ≤ g b)
              → ((b b′ : 𝓑) → b ≤ b′ → g b ≤ g b′)
              → (x : 𝓑) (k : ℕ) → iter f x k ≤ iter g x k
iter-dominate         f≤g g-mono x zero     = ≤-refl x
iter-dominate {f} {g} f≤g g-mono x (succ k) =
 ≤-trans (f≤g (iter f x k))
         (g-mono (iter f x k) (iter g x k) (iter-dominate f≤g g-mono x k))

\end{code}

Doubling is absorbed by *every* `ω`-power `ω^(X ⊗ ω)` with `X` positive — the
multipliers the orbit itself produces (below). `ω^(X ⊗ ω) = L (λ k → ω^(X ⊗
ι[k]))`, and each `ι[2] ⊗ ω^(X ⊗ ι[k]) ≤ ω ⊗ ω^(X ⊗ ι[k]) = ω^(ι[1] ⊕ X ⊗ ι[k])
≤ ω^(X ⊗ ι[succ k])` (`ι[1] ⊕ β ≤ S β ≤ β ⊕ X` since `X ≥ 1`, via `S⊕≤S`), which
sits at the next index of the limit. So `ι[2] ⊗ ω^(X ⊗ ω) ≤ ω^(X ⊗ ω)` — the
doubling-absorption for the whole `ω`-power tower, not just `ω`.

\begin{code}

dbl-ω^ : (X : 𝓑) → S Z ≤ X → (ι[ 2 ] ⊗ ω^ (X ⊗ ω)) ≤ ω^ (X ⊗ ω)
dbl-ω^ X X+ = ≤-L per
 where
  per : (k : ℕ) → (ι[ 2 ] ⊗ ω^ (X ⊗ ι[ k ])) ≤ ω^ (X ⊗ ω)
  per k = ≤-trans step-a
            (transport (λ z → z ≤ ω^ (X ⊗ ω)) (step-b ⁻¹)
                       (≤-trans step-c step-d))
   where
    A : 𝓑
    A = ω^ (X ⊗ ι[ k ])

    step-a : (ι[ 2 ] ⊗ A) ≤ (ω ⊗ A)
    step-a = ⊗-mono-left (≤-L-upper-bound ι[_] 2) A

    step-b : (ω ⊗ A) ＝ ω^ (ι[ 1 ] ⊕ (X ⊗ ι[ k ]))
    step-b = ap (_⊗ A) ((ω^-ι1) ⁻¹) ∙ ω^⊗ ι[ 1 ] (X ⊗ ι[ k ])

    exp-le : (ι[ 1 ] ⊕ (X ⊗ ι[ k ])) ≤ (X ⊗ ι[ succ k ])
    exp-le = ≤-trans (S⊕≤S (X ⊗ ι[ k ]))
                     (⊕-mono-right (X ⊗ ι[ k ]) X+)

    step-c : ω^ (ι[ 1 ] ⊕ (X ⊗ ι[ k ])) ≤ ω^ (X ⊗ ι[ succ k ])
    step-c = ω^-mono exp-le

    step-d : ω^ (X ⊗ ι[ succ k ]) ≤ ω^ (X ⊗ ω)
    step-d = ≤-L-upper-bound (λ j → ω^ (X ⊗ ι[ j ])) (succ k)

\end{code}

Fix a multiplier `M` that is positive (`S Z ≤ M`) and absorbs doubling
(`ι[2] ⊗ M ≤ M`).

\begin{code}

module _ (M : 𝓑) (M+ : S Z ≤ M) (dbl : (ι[ 2 ] ⊗ M) ≤ M) where

\end{code}

The crux. If `c ≤ Y` then `(Y ⊕ c) ⊗ M ≤ Y ⊗ M`: bound `Y ⊕ c` by
`Y ⊕ Y = Y ⊗ ι[2]`, associate, and absorb `ι[2] ⊗ M` back to `M`. No
`affine-fold` — the multiplier stays `M` throughout.

\begin{code}

 crux : (Y c : 𝓑) → c ≤ Y → ((Y ⊕ c) ⊗ M) ≤ (Y ⊗ M)
 crux Y c c≤Y = ≤-trans (⊗-mono-left step12 M) final
  where
   Yι2=YY : (Y ⊗ ι[ 2 ]) ＝ (Y ⊕ Y)
   Yι2=YY = ap (_⊕ Y) (Z-left-unit Y)

   step12 : (Y ⊕ c) ≤ (Y ⊗ ι[ 2 ])
   step12 = transport ((Y ⊕ c) ≤_) (Yι2=YY ⁻¹) (⊕-mono-right Y c≤Y)

   final : ((Y ⊗ ι[ 2 ]) ⊗ M) ≤ (Y ⊗ M)
   final = transport (_≤ (Y ⊗ M)) ((⊗-assoc Y ι[ 2 ] M) ⁻¹)
                     (⊗-mono-right Y dbl)

\end{code}

The limit-multiplier affine body, and its orbit invariant: the `k`-th iterate
is bounded by the start-plus-constant, scaled by the `k`-th power `Mᵏ`
(`MultOrbit.pw`). Base: `M⁰ = 1` is the (left) unit. Step: the incoming `c`
sits below `Y = (a ⊕ c) ⊗ Mᵏ` (as `Mᵏ ≥ 1`), so `crux` absorbs it and
`⊗-assoc` folds `Y ⊗ M` into `(a ⊕ c) ⊗ Mᵏ⁺¹`.

\begin{code}

 mbody : 𝓑 → 𝓑 → 𝓑
 mbody c b = (b ⊕ c) ⊗ M

 pw-pos : (k : ℕ) → S Z ≤ pw M k
 pw-pos zero     = ≤-refl (S Z)
 pw-pos (succ k) = ≤-trans (pw-pos k)
                    (transport (_≤ (pw M k ⊗ M)) (Z-left-unit (pw M k))
                       (⊗-mono-right (pw M k) M+))

 orbit-inv : (a c : 𝓑) (k : ℕ) → iter (mbody c) a k ≤ ((a ⊕ c) ⊗ pw M k)
 orbit-inv a c zero     =
  transport (a ≤_) ((Z-left-unit (a ⊕ c)) ⁻¹) (⊕-increasing-right a c)
 orbit-inv a c (succ k) =
  transport (λ z → iter (mbody c) a (succ k) ≤ z) step-eq
            (≤-trans body-mono (crux Y c c≤Y))
  where
   Y : 𝓑
   Y = (a ⊕ c) ⊗ pw M k

   body-mono : ((iter (mbody c) a k ⊕ c) ⊗ M) ≤ ((Y ⊕ c) ⊗ M)
   body-mono = ⊗-mono-left (⊕-mono-left (orbit-inv a c k) c) M

   c≤Y : c ≤ Y
   c≤Y = ≤-trans (⊕-increasing-left a c)
                 (transport (_≤ Y) (Z-left-unit (a ⊕ c))
                    (⊗-mono-right (a ⊕ c) (pw-pos k)))

   step-eq : (Y ⊗ M) ＝ ((a ⊕ c) ⊗ pw M (succ k))
   step-eq = ⊗-assoc (a ⊕ c) (pw M k) M

\end{code}

The payoff: a limit-multiplier affine orbit is `< ε₀` for any multiplier
`M < ε₀`. The supremum `L (λ k → (a ⊕ c) ⊗ pw M k)` is `(a ⊕ c) ⊗ L (pw M)`
*definitionally*, and `L (pw M) < ε₀` (`MultOrbit.pw-sup-<-ε₀`, the sup of the
powers `= ω^(M ⊗ ω)`), with `a ⊕ c < ε₀`, by `⊗-<-ε₀`.

\begin{code}

 mult-affine-orbit-<-ε₀ : (a c : 𝓑) → a < ε₀ → c < ε₀ → M < ε₀
                        → L (λ k → iter (mbody c) a k) < ε₀
 mult-affine-orbit-<-ε₀ a c a<ε₀ c<ε₀ M<ε₀ =
  ≤-trans (≤-S (≤-L-mono (orbit-inv a c)))
          (⊗-<-ε₀ (a ⊕ c) (L (pw M))
                  (⊕-<-ε₀ a c a<ε₀ c<ε₀)
                  (pw-sup-<-ε₀ M M<ε₀))

\end{code}

The headline instance, `M = ω`. The body `b ↦ (b ⊕ c) ⊗ ω` is the shape of the
start-varying recursor majorant's leading term; its orbit is `< ε₀`, reaching
`ω^(ω ⊗ ω)` — a limit-multiplier iteration bounded, past the finite-`Aff`
ceiling.

\begin{code}

ω-pos : S Z ≤ ω
ω-pos = ≤-L-upper-bound ι[_] 1

mult-ω-orbit-<-ε₀ : (a c : 𝓑) → a < ε₀ → c < ε₀
                  → L (λ k → iter (λ b → (b ⊕ c) ⊗ ω) a k) < ε₀
mult-ω-orbit-<-ε₀ a c a<ε₀ c<ε₀ =
 mult-affine-orbit-<-ε₀ ω ω-pos (ιn⊗ω-≤-ω 2) a c a<ε₀ c<ε₀ (tower-<-ε₀ 0)

\end{code}

Connecting to the recursor. `Affine.affine-orbit-≤` bounds the *start-varying
recursor majorant* `σ a = L (λ j → iter φ a j)` — the height of "run the
recursor `φ` from start `a`" — by exactly `(a ⊕ d ⊗ ω) ⊗ ω`, i.e. the
limit-affine body `b ↦ (b ⊕ d ⊗ ω) ⊗ ω`. So *iterating* `σ` — nesting the
recursor on its own running start, the canonical single-nesting tower term — is
dominated (`iter-dominate`, that body being monotone) by an `M = ω` orbit, and
hence has supremum `< ε₀`. This is a genuine start-varying recursor nesting
bounded through iteration, past the finite-`Aff` ceiling — the affine-fold wall
did not stop it.

\begin{code}

recursor-start-orbit-<-ε₀ :
   (φ : 𝓑 → 𝓑) (d : 𝓑) (p : ℕ)
 → ((b : 𝓑) → φ b ≤ ((b ⊕ d) ⊗ ι[ succ p ]))
 → d < ε₀
 → (x : 𝓑) → x < ε₀
 → L (λ k → iter (λ a → L (λ j → iter φ a j)) x k) < ε₀
recursor-start-orbit-<-ε₀ φ d p aff d<ε₀ x x<ε₀ =
 ≤-trans (≤-S (≤-L-mono (iter-dominate σ≤g g-mono x)))
         (mult-ω-orbit-<-ε₀ x (d ⊗ ω) x<ε₀ (⊗-<-ε₀ d ω d<ε₀ (tower-<-ε₀ 0)))
 where
  g : 𝓑 → 𝓑
  g b = (b ⊕ (d ⊗ ω)) ⊗ ω

  g-mono : (b b′ : 𝓑) → b ≤ b′ → g b ≤ g b′
  g-mono b b′ b≤b′ = ⊗-mono-left (⊕-mono-left b≤b′ (d ⊗ ω)) ω

  σ≤g : (a : 𝓑) → L (λ j → iter φ a j) ≤ g a
  σ≤g a = affine-orbit-≤ φ d p aff a

\end{code}

Nesting composes — the tower's arithmetic. The orbit of an `M`-body is bounded
by an `mbody` again, at the *raised* multiplier `M' = ω^(M ⊗ ω)`:

  `mbody-orbit-≤ : L (λ k → iter (mbody M c) a k) ≤ (a ⊕ c) ⊗ ω^(M ⊗ ω)`,

since `L (λ k → (a ⊕ c) ⊗ Mᵏ) = (a ⊕ c) ⊗ L (pw M)` and `L (pw M) ≤ ω^(M ⊗ ω)`.
And `M' = ω^(M ⊗ ω)` is *again a valid multiplier* — positive (`one-≤-ω^`),
doubling-absorbing (`dbl-ω^`), and `< ε₀` for `M < ε₀`. So the class of
limit-multiplier bodies is **closed under taking orbits**: each recursor-nesting
level raises the multiplier `M ↦ ω^(M ⊗ ω)`, and every *finite* nesting stays
`< ε₀`. This is the arithmetic of the type-level tower — one exponentiation per
level, finitely many below `ε₀` — with no `affine-fold` and no ceiling.

\begin{code}

mbody-orbit-≤ : (M : 𝓑) (M+ : S Z ≤ M) (dbl : (ι[ 2 ] ⊗ M) ≤ M) (c a : 𝓑)
              → L (λ k → iter (λ b → (b ⊕ c) ⊗ M) a k)
                ≤ ((a ⊕ c) ⊗ ω^ (M ⊗ ω))
mbody-orbit-≤ M M+ dbl c a =
 ≤-trans (≤-L-mono (orbit-inv M M+ dbl a c))
         (⊗-mono-right (a ⊕ c) (pw-sup-≤ M))

\end{code}

The two-level witness (the general `n`-level nesting is the same threading, with
`M ↦ ω^(M ⊗ ω)` composed with itself). *Iterating* "run the `M`-body recursor
from the current start" — the composed nesting — is `< ε₀`, at the raised
multiplier `M' = ω^(M ⊗ ω)`: the inner orbit majorant is pointwise below the
monotone `M'`-body (`mbody-orbit-≤`), so `iter-dominate` reduces it to an
`M'`-orbit, which `mult-affine-orbit-<-ε₀` bounds.

\begin{code}

nest2-<-ε₀ : (M : 𝓑) (M+ : S Z ≤ M) (dbl : (ι[ 2 ] ⊗ M) ≤ M) → M < ε₀
           → (c a : 𝓑) → a < ε₀ → c < ε₀
           → L (λ j → iter (λ x → L (λ k → iter (λ b → (b ⊕ c) ⊗ M) x k)) a j)
             < ε₀
nest2-<-ε₀ M M+ dbl M<ε₀ c a a<ε₀ c<ε₀ =
 ≤-trans (≤-S (≤-L-mono (iter-dominate σ≤g′ g′-mono a)))
         (mult-affine-orbit-<-ε₀ M′ M′+ M′dbl a c a<ε₀ c<ε₀ M′<ε₀)
 where
  M′ : 𝓑
  M′ = ω^ (M ⊗ ω)

  M′+ : S Z ≤ M′
  M′+ = one-≤-ω^ (M ⊗ ω)

  M′dbl : (ι[ 2 ] ⊗ M′) ≤ M′
  M′dbl = dbl-ω^ M M+

  M′<ε₀ : M′ < ε₀
  M′<ε₀ = ω^-<-ε₀ (M ⊗ ω) (⊗-<-ε₀ M ω M<ε₀ (tower-<-ε₀ 0))

  g′ : 𝓑 → 𝓑
  g′ x = (x ⊕ c) ⊗ M′

  g′-mono : (x x′ : 𝓑) → x ≤ x′ → g′ x ≤ g′ x′
  g′-mono x x′ x≤x′ = ⊗-mono-left (⊕-mono-left x≤x′ c) M′

  σ≤g′ : (x : 𝓑) → L (λ k → iter (λ b → (b ⊕ c) ⊗ M) x k) ≤ g′ x
  σ≤g′ x = mbody-orbit-≤ M M+ dbl c x

\end{code}

The multiplier tower, made explicit. Starting from `ω`, each nesting level
raises the multiplier by `M ↦ ω^(M ⊗ ω)`. Every level is a *valid* multiplier —
positive, doubling-absorbing, and `< ε₀` — so a limit-multiplier orbit at *any*
finite level of the tower is `< ε₀`. This is the type-level tower `ω ↑↑ ℓ`
realised as an inexhaustible-below-`ε₀` sequence of multipliers, each obtained
from the last by one `ω`-exponentiation, all validated by pure Brouwer-code
arithmetic.

\begin{code}

Mult : ℕ → 𝓑
Mult zero     = ω
Mult (succ s) = ω^ (Mult s ⊗ ω)

Mult-pos : (s : ℕ) → S Z ≤ Mult s
Mult-pos zero     = ω-pos
Mult-pos (succ s) = one-≤-ω^ (Mult s ⊗ ω)

Mult-dbl : (s : ℕ) → (ι[ 2 ] ⊗ Mult s) ≤ Mult s
Mult-dbl zero     = ιn⊗ω-≤-ω 2
Mult-dbl (succ s) = dbl-ω^ (Mult s) (Mult-pos s)

Mult-<-ε₀ : (s : ℕ) → Mult s < ε₀
Mult-<-ε₀ zero     = tower-<-ε₀ 0
Mult-<-ε₀ (succ s) =
 ω^-<-ε₀ (Mult s ⊗ ω) (⊗-<-ε₀ (Mult s) ω (Mult-<-ε₀ s) (tower-<-ε₀ 0))

mult-tower-orbit-<-ε₀ : (s : ℕ) (c a : 𝓑) → a < ε₀ → c < ε₀
                      → L (λ k → iter (λ b → (b ⊕ c) ⊗ Mult s) a k) < ε₀
mult-tower-orbit-<-ε₀ s c a a<ε₀ c<ε₀ =
 mult-affine-orbit-<-ε₀ (Mult s) (Mult-pos s) (Mult-dbl s) a c a<ε₀ c<ε₀
                        (Mult-<-ε₀ s)

\end{code}
