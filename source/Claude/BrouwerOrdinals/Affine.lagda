Orbit suprema for affine majorants: tools, the multiplicative case, and the
precise obstruction (constructive).

This works toward the last step of the first-order theorem — that the
compositional majorant `μ t` of `DialogueTreeHeight.Majorant` is `< ε₀`. By
the fundamental theorem `height ⟦t⟧ ≤ μ t`, so `μ t < ε₀` would finish the
first-order `< ε₀` bound. The majorant is built from `Z, S, ⊕` and the
recursor's **orbit supremum** `μ-Iter φ a ν = (sup_k φᵏ a) ⊕ ν`; everything
reduces to bounding orbit suprema `L (λ k → iter φ a k)` for the
ι⇒ι-majorant `φ`.

What this module establishes:

* **Left distributivity** `c ⊗ (x ⊕ y) = (c ⊗ x) ⊕ (c ⊗ y)` (the ordinal
  product distributes over the sum on the *left*);
* `a ⊗ ω < ε₀` for `a < ε₀` (`⊗ω-<-ε₀`): one factor of `ω` stays below `ε₀`;
* **the multiplicative orbit is `< ε₀`** (`double-orbit-<-ε₀`): iterating the
  doubling majorant `b ↦ b ⊕ b` has orbit supremum `≤ a ⊗ ω < ε₀`. This is
  the case once feared to escape (a `φ` that *multiplies* the height): it is
  controlled, because `k`-fold doubling is `⊗ ι[2ᵏ]` with `2ᵏ` finite, hence
  `≤ ⊗ ω` — *one* factor of `ω`, never an exponential. The proof rides on
  left distributivity and `ι[m+n] = ι[m] ⊕ ι[n]`.

The composition obstruction, and why it is **not** fundamental. The naive
affine form `φ b ≤ b ⊗ ι[p] ⊕ d` (constant *outside*) does not compose:
that would need right distributivity `(x ⊕ y) ⊗ p ≤ x ⊗ p ⊕ y ⊗ p`, which is
*false* for the non-commutative ordinal product (e.g. `(1 ⊕ ω) ⊗ 2 =
1 ⊕ ω ⊕ 1 ⊕ ω`, while `1 ⊗ 2 ⊕ ω ⊗ 2 = 1 ⊕ 1 ⊕ ω ⊕ ω`, and
`ω ⊕ 1 ⊕ ω ≠ ω ⊕ ω`). The fix is to keep the constant **inside**: the form
`φ b ≤ (b ⊕ d) ⊗ ι[p]` *does* compose, using only **left** distributivity
and the **fold lemma** `affine-fold` below (`x ⊗ ι[p+1] ⊕ d ≤ (x ⊕ d) ⊗
ι[p+1]`). Concretely, for `φ b ≤ (b ⊕ d) ⊗ ι[p]`, `ψ b ≤ (b ⊕ e) ⊗ ι[q]`:
`φ(ψ b) ≤ (ψ b ⊕ d) ⊗ ι[p] ≤ ((b ⊕ e) ⊗ ι[q] ⊕ d) ⊗ ι[p]
        ≤ (((b ⊕ e) ⊕ d) ⊗ ι[q]) ⊗ ι[p] = (b ⊕ (e ⊕ d)) ⊗ ι[qp]`
(fold, then `⊗`-associativity) — affine again, **no natural sum needed**.

So the path to `μ t < ε₀` is open via Brouwer-code arithmetic. The **general
affine-orbit bound is now proved** here (`affine-orbit-<-ε₀`): for any affine
`φ b ≤ (b ⊕ d) ⊗ ι[p+1]` with `d < ε₀`, the orbit supremum
`sup_k φᵏ a ≤ (a ⊕ d ⊗ ω) ⊗ ω < ε₀` whenever `a < ε₀` — folding the constant
in via `affine-fold` and `⊗`-associativity, then absorbing `ι[(p+1)ᵏ] ≤ ω`.
This is exactly the bound the recursor majorant `μ-Iter` of
`DialogueTreeHeight.Majorant` needs (`double-orbit-<-ε₀` is the constant-free
instance).

What remains for `μ t < ε₀` is the **hereditary affine closure**: that the
majorant `μ F` of every first-order `F : ι⇒ι` is affine in the above sense
(so the orbit lemma applies). Because the combinator `S` can build an `ι⇒ι`
majorant `λa. φ a (γ a)` whose affineness in `a` depends on the
sub-functionals `φ, γ`, this requires propagating affineness *hereditarily*
through all first-order types — Howard's hereditarily-majorizable
functionals. That is the one substantial piece still to formalise; the
arithmetic it rests on (the orbit bound, `affine-fold`, `⊗ω-<-ε₀`) is all
here.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.BrouwerOrdinals.Affine
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import Claude.BrouwerOrdinals.Order fe
open import Claude.BrouwerOrdinals.Orbit fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-assoc ; ⊕-mono-left)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; tower ; ε₀ ; tower-<-ε₀ ; tower-strict ; S-increasing ;
        ⊕-mono-right ; ⊕-increasing-right ; ⊗-mono-left ; ⊗-mono-right ;
        Z-left-unit ; ω^_ ; ω^-mono ; ω^-ι1 ; ⊕-<-ε₀)

\end{code}

Left distributivity of `⊗` over `⊕` (the product recurses on its right
argument, compatibly with the sum).

\begin{code}

⊗-left-distrib : (c x y : 𝓑) → (c ⊗ (x ⊕ y)) ＝ ((c ⊗ x) ⊕ (c ⊗ y))
⊗-left-distrib c x Z     = refl
⊗-left-distrib c x (S y) = ap (_⊕ c) (⊗-left-distrib c x y)
                         ∙ ⊕-assoc (c ⊗ x) (c ⊗ y) c
⊗-left-distrib c x (L f) = ap L (dfunext fe (λ n → ⊗-left-distrib c x (f n)))

\end{code}

Left-addition is inflationary (`x ≤ d ⊕ x`), and the **fold lemma**: an
additive constant on the *outside* of a finite product can be folded to the
*inside* — `x ⊗ ι[p+1] ⊕ d ≤ (x ⊕ d) ⊗ ι[p+1]`. This is the lemma that
sidesteps the failure of right distributivity: with the constant kept inside
(`(b ⊕ d) ⊗ ι[p]`), affine maps *do* compose, using only left distributivity
and this fold (no right distributivity, no natural sum).

\begin{code}

⊕-increasing-left : (d x : 𝓑) → x ≤ (d ⊕ x)
⊕-increasing-left d Z     = ≤-Z
⊕-increasing-left d (S x) = ≤-S (⊕-increasing-left d x)
⊕-increasing-left d (L f) = ≤-L-mono (λ n → ⊕-increasing-left d (f n))

affine-fold : (x d : 𝓑) (p : ℕ)
            → (x ⊗ ι[ succ p ] ⊕ d) ≤ ((x ⊕ d) ⊗ ι[ succ p ])
affine-fold x d p =
 transport (λ z → z ≤ ((x ⊕ d) ⊗ ι[ succ p ]))
           ((⊕-assoc (x ⊗ ι[ p ]) x d) ⁻¹)
           (⊕-mono-left (⊗-mono-left (⊕-increasing-right x d) ι[ p ]) (x ⊕ d))

\end{code}

One factor of `ω` keeps us below `ε₀`.

\begin{code}

tower-⊗-ω : (n : ℕ) → (tower n ⊗ ω) ≤ tower (succ n)
tower-⊗-ω zero     = transport (λ z → (z ⊗ ω) ≤ tower 1) ω^-ι1
                               (ω^-mono (≤-L-upper-bound ι[_] 2))
tower-⊗-ω (succ m) = ω^-mono (tower-strict m)

⊗ω-<-ε₀ : (a : 𝓑) → a < ε₀ → (a ⊗ ω) < ε₀
⊗ω-<-ε₀ a (≤-ℓ n q) = ≤-trans (≤-S aω≤) (tower-<-ε₀ (succ n))
 where
  a≤ : a ≤ tower n
  a≤ = ≤-trans (S-increasing a) q

  aω≤ : (a ⊗ ω) ≤ tower (succ n)
  aω≤ = ≤-trans (⊗-mono-left a≤ ω) (tower-⊗-ω n)

\end{code}

Numeral arithmetic: addition and the homomorphism `ι[m+n] = ι[m] ⊕ ι[n]`.

\begin{code}

_+ℕ_ : ℕ → ℕ → ℕ
m +ℕ zero   = m
m +ℕ succ n = succ (m +ℕ n)

ι-+-homo : (m n : ℕ) → ι[ m +ℕ n ] ＝ (ι[ m ] ⊕ ι[ n ])
ι-+-homo m zero     = refl
ι-+-homo m (succ n) = ap S (ι-+-homo m n)

\end{code}

The multiplicative orbit. Iterating the doubling majorant `double b = b ⊕ b`
is `⊗ ι[2ᵏ]`, hence bounded by `⊗ ω` and so `< ε₀`.

\begin{code}

double : 𝓑 → 𝓑
double b = b ⊕ b

pow2 : ℕ → ℕ
pow2 zero     = 1
pow2 (succ k) = pow2 k +ℕ pow2 k

double-orbit-≤ : (a : 𝓑) (k : ℕ) → iter double a k ≤ (a ⊗ ι[ pow2 k ])
double-orbit-≤ a zero     =
 transport (a ≤_) ((Z-left-unit a) ⁻¹) (≤-refl a)
double-orbit-≤ a (succ k) =
 transport (λ z → iter double a (succ k) ≤ z) eq step
 where
  IH : iter double a k ≤ (a ⊗ ι[ pow2 k ])
  IH = double-orbit-≤ a k

  step : iter double a (succ k)
       ≤ ((a ⊗ ι[ pow2 k ]) ⊕ (a ⊗ ι[ pow2 k ]))
  step = ≤-trans (⊕-mono-left IH (iter double a k))
                 (⊕-mono-right (a ⊗ ι[ pow2 k ]) IH)

  eq : ((a ⊗ ι[ pow2 k ]) ⊕ (a ⊗ ι[ pow2 k ])) ＝ (a ⊗ ι[ pow2 (succ k) ])
  eq = (⊗-left-distrib a ι[ pow2 k ] ι[ pow2 k ]) ⁻¹
     ∙ ap (a ⊗_) ((ι-+-homo (pow2 k) (pow2 k)) ⁻¹)

double-orbit-sup-≤ : (a : 𝓑) → L (λ k → iter double a k) ≤ (a ⊗ ω)
double-orbit-sup-≤ a =
 ≤-L (λ k → ≤-trans (double-orbit-≤ a k)
                    (⊗-mono-right a (≤-L-upper-bound ι[_] (pow2 k))))

double-orbit-<-ε₀ : (a : 𝓑) → a < ε₀ → L (λ k → iter double a k) < ε₀
double-orbit-<-ε₀ a a<ε₀ =
 ≤-trans (≤-S (double-orbit-sup-≤ a)) (⊗ω-<-ε₀ a a<ε₀)

\end{code}

Toward the general affine orbit: `⊗`-associativity, `ι` multiplicativity,
and the fold lemma for a numeral multiplier (positive).

\begin{code}

⊗-assoc : (a b c : 𝓑) → ((a ⊗ b) ⊗ c) ＝ (a ⊗ (b ⊗ c))
⊗-assoc a b Z     = refl
⊗-assoc a b (S c) = ap (_⊕ (a ⊗ b)) (⊗-assoc a b c)
                  ∙ (⊗-left-distrib a (b ⊗ c) b) ⁻¹
⊗-assoc a b (L f) = ap L (dfunext fe (λ n → ⊗-assoc a b (f n)))

_·ℕ_ : ℕ → ℕ → ℕ
m ·ℕ zero   = zero
m ·ℕ succ n = (m ·ℕ n) +ℕ m

ι-*-homo : (m n : ℕ) → (ι[ m ] ⊗ ι[ n ]) ＝ ι[ m ·ℕ n ]
ι-*-homo m zero     = refl
ι-*-homo m (succ n) = ap (_⊕ ι[ m ]) (ι-*-homo m n) ∙ (ι-+-homo (m ·ℕ n) m) ⁻¹

affine-fold-num : (x d : 𝓑) (m : ℕ) → S Z ≤ ι[ m ]
                → (x ⊗ ι[ m ] ⊕ d) ≤ ((x ⊕ d) ⊗ ι[ m ])
affine-fold-num x d (succ m) _ = affine-fold x d m
affine-fold-num x d zero     ()

\end{code}

One is below any product of positives. Then the **general affine orbit**:
for an affine `φ b ≤ (b ⊕ d) ⊗ ι[p+1]`, the orbit `iter φ a k` is bounded by
`(a ⊕ d ⊗ ι[k]) ⊗ ι[(p+1)ᵏ]`, so its supremum is `≤ (a ⊕ d ⊗ ω) ⊗ ω < ε₀`.
This is the closure the recursor majorant `μ-Iter` needs.

\begin{code}

one-≤-⊗ : (x y : 𝓑) → S Z ≤ x → S Z ≤ y → S Z ≤ (x ⊗ y)
one-≤-⊗ x y hx hy =
 ≤-trans hx (≤-trans (transport (x ≤_) ((Z-left-unit x) ⁻¹) (≤-refl x))
                     (⊗-mono-right x hy))

module _ (φ : 𝓑 → 𝓑) (d : 𝓑) (p : ℕ)
         (φ-affine : (b : 𝓑) → φ b ≤ ((b ⊕ d) ⊗ ι[ succ p ]))
       where

 g : 𝓑 → 𝓑
 g b = (b ⊕ d) ⊗ ι[ succ p ]

 g-mono : {x y : 𝓑} → x ≤ y → g x ≤ g y
 g-mono x≤y = ⊗-mono-left (⊕-mono-left x≤y d) ι[ succ p ]

 iter-φ-≤-g : (a : 𝓑) (k : ℕ) → iter φ a k ≤ iter g a k
 iter-φ-≤-g a zero     = ≤-refl a
 iter-φ-≤-g a (succ k) =
  ≤-trans (φ-affine (iter φ a k)) (g-mono (iter-φ-≤-g a k))

 Qpow : ℕ → ℕ
 Qpow zero     = 1
 Qpow (succ k) = Qpow k ·ℕ succ p

 Qpow-pos : (k : ℕ) → S Z ≤ ι[ Qpow k ]
 Qpow-pos zero     = ≤-S ≤-Z
 Qpow-pos (succ k) =
  transport (S Z ≤_) (ι-*-homo (Qpow k) (succ p))
            (one-≤-⊗ ι[ Qpow k ] ι[ succ p ] (Qpow-pos k) (≤-S ≤-Z))

 g-orbit-≤ : (a : 𝓑) (k : ℕ)
           → iter g a k ≤ ((a ⊕ (d ⊗ ι[ k ])) ⊗ ι[ Qpow k ])
 g-orbit-≤ a zero     = transport (a ≤_) ((Z-left-unit a) ⁻¹) (≤-refl a)
 g-orbit-≤ a (succ k) =
  transport (λ z → iter g a (succ k) ≤ (z ⊗ ι[ Qpow (succ k) ]))
            (⊕-assoc a (d ⊗ ι[ k ]) d)
            bound
  where
   W : 𝓑
   W = (a ⊕ (d ⊗ ι[ k ])) ⊕ d

   chain : iter g a (succ k) ≤ ((W ⊗ ι[ Qpow k ]) ⊗ ι[ succ p ])
   chain =
    ≤-trans (⊗-mono-left (⊕-mono-left (g-orbit-≤ a k) d) ι[ succ p ])
            (⊗-mono-left
              (affine-fold-num (a ⊕ (d ⊗ ι[ k ])) d (Qpow k) (Qpow-pos k))
              ι[ succ p ])

   assoc-mult : ((W ⊗ ι[ Qpow k ]) ⊗ ι[ succ p ]) ＝ (W ⊗ ι[ Qpow (succ k) ])
   assoc-mult = ⊗-assoc W ι[ Qpow k ] ι[ succ p ]
              ∙ ap (W ⊗_) (ι-*-homo (Qpow k) (succ p))

   bound : iter g a (succ k) ≤ (W ⊗ ι[ Qpow (succ k) ])
   bound = transport (λ z → iter g a (succ k) ≤ z) assoc-mult chain

 orbit-sup-≤ : (a : 𝓑) → L (λ k → iter g a k) ≤ ((a ⊕ (d ⊗ ω)) ⊗ ω)
 orbit-sup-≤ a = ≤-L (λ k → ≤-trans (g-orbit-≤ a k) (per-term k))
  where
   per-term : (k : ℕ)
            → ((a ⊕ (d ⊗ ι[ k ])) ⊗ ι[ Qpow k ]) ≤ ((a ⊕ (d ⊗ ω)) ⊗ ω)
   per-term k =
    ≤-trans (⊗-mono-left
               (⊕-mono-right a (⊗-mono-right d (≤-L-upper-bound ι[_] k)))
               ι[ Qpow k ])
            (⊗-mono-right (a ⊕ (d ⊗ ω)) (≤-L-upper-bound ι[_] (Qpow k)))

 affine-orbit-≤ : (a : 𝓑) → L (λ k → iter φ a k) ≤ ((a ⊕ (d ⊗ ω)) ⊗ ω)
 affine-orbit-≤ a = ≤-trans (≤-L-mono (iter-φ-≤-g a)) (orbit-sup-≤ a)

 affine-orbit-<-ε₀ : d < ε₀ → (a : 𝓑) → a < ε₀ → L (λ k → iter φ a k) < ε₀
 affine-orbit-<-ε₀ d<ε₀ a a<ε₀ =
  ≤-trans (≤-S (affine-orbit-≤ a))
          (⊗ω-<-ε₀ (a ⊕ (d ⊗ ω)) (⊕-<-ε₀ a (d ⊗ ω) a<ε₀ (⊗ω-<-ε₀ d d<ε₀)))

\end{code}
