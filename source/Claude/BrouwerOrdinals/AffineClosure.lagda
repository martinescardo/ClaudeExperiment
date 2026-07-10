Closure of the affine class (constructive).

Toward `μ t < ε₀`: the recursor majorant's orbit suprema are bounded for
*affine* `ι⇒ι` majorants (`Claude.BrouwerOrdinals.Affine.affine-orbit-<-ε₀`).
This module collects the closure properties of the affine class `Aff` — the
`ι⇒ι` majorants that arise are affine, and `Aff` is closed under composition
and pointwise sum.

`Aff φ` says `φ b ≤ (b ⊕ d) ⊗ ι[m]` for a fixed `d < ε₀` and a *positive*
finite multiplier `ι[m]` (`S Z ≤ ι[m]`). Keeping the multiplier as a bare
numeral (with a positivity proof) rather than `ι[p+1]` lets the closure
proofs multiply multipliers (`ι[m] ⊗ ι[n] = ι[m·n]`) without `succ`
bookkeeping. The constant is kept *inside* the product — the form that
composes (see `Affine.affine-fold`).

These are the building blocks the hereditary closure assembles; each is
proved here outright from the arithmetic of `Affine`/`Epsilon0`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.BrouwerOrdinals.AffineClosure
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import Claude.BrouwerOrdinals.Order fe
open import Claude.BrouwerOrdinals.Orbit fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-assoc ; ⊕-mono-left)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; tower ; tower-<-ε₀ ; ⊕-<-ε₀ ; ⊕-mono-right ;
        ⊕-increasing-right ; ⊗-mono-left ; ⊗-mono-right ; Z-left-unit)
open import Claude.BrouwerOrdinals.Affine fe
 using (affine-fold-num ; ⊗-assoc ; _·ℕ_ ; ι-*-homo ; ⊕-increasing-left ;
        ⊗ω-<-ε₀ ; affine-orbit-<-ε₀ ; one-≤-⊗)

\end{code}

Small arithmetic helpers: `1 ⊗ y = y`, and a code is below itself times a
positive code on either side.

\begin{code}

SZ-⊗ : (y : 𝓑) → ((S Z) ⊗ y) ＝ y
SZ-⊗ Z     = refl
SZ-⊗ (S y) = ap S (SZ-⊗ y)
SZ-⊗ (L f) = ap L (dfunext fe (λ n → SZ-⊗ (f n)))

x-≤-x⊗ : (x y : 𝓑) → S Z ≤ y → x ≤ (x ⊗ y)
x-≤-x⊗ x y y+ =
 ≤-trans (transport (x ≤_) ((Z-left-unit x) ⁻¹) (≤-refl x)) (⊗-mono-right x y+)

y-≤-⊗ : (x y : 𝓑) → S Z ≤ x → y ≤ (x ⊗ y)
y-≤-⊗ x y x+ = transport (_≤ (x ⊗ y)) (SZ-⊗ y) (⊗-mono-left x+ y)

\end{code}

The affine class, and that small ordinals are `< ε₀`.

\begin{code}

Aff : (𝓑 → 𝓑) → 𝓤₀ ̇
Aff φ = Σ m ꞉ ℕ , Σ d ꞉ 𝓑 ,
          (S Z ≤ ι[ m ]) × (d < ε₀) × ((b : 𝓑) → φ b ≤ ((b ⊕ d) ⊗ ι[ m ]))

ι<ε₀ : (m : ℕ) → ι[ m ] < ε₀
ι<ε₀ m = ≤-trans (≤-S (≤-L-upper-bound ι[_] m)) (tower-<-ε₀ 0)

Z<ε₀ : Z < ε₀
Z<ε₀ = ι<ε₀ 0

⊗ι-<-ε₀ : (a : 𝓑) (m : ℕ) → a < ε₀ → (a ⊗ ι[ m ]) < ε₀
⊗ι-<-ε₀ a m a<ε₀ =
 ≤-trans (≤-S (⊗-mono-right a (≤-L-upper-bound ι[_] m))) (⊗ω-<-ε₀ a a<ε₀)

\end{code}

An affine majorant applied to a sub-`ε₀` input stays `< ε₀`.

\begin{code}

Aff-app : {φ : 𝓑 → 𝓑} → Aff φ → (x : 𝓑) → x < ε₀ → φ x < ε₀
Aff-app (m , d , _ , d<ε₀ , bound) x x<ε₀ =
 ≤-trans (≤-S (bound x)) (⊗ι-<-ε₀ (x ⊕ d) m (⊕-<-ε₀ x d x<ε₀ d<ε₀))

\end{code}

The base affine majorants: identity (`Succ`), successor (`Ω`), and constants
(`K`).

\begin{code}

Aff-id : Aff (λ b → b)
Aff-id = 1 , Z , ≤-S ≤-Z , Z<ε₀ ,
         (λ b → transport (b ≤_) ((Z-left-unit b) ⁻¹) (≤-refl b))

Aff-S : Aff (λ b → S b)
Aff-S = 1 , ι[ 1 ] , ≤-S ≤-Z , ι<ε₀ 1 ,
        (λ b → transport ((S b) ≤_) ((Z-left-unit (S b)) ⁻¹) (≤-refl (S b)))

const-Aff : (x : 𝓑) → x < ε₀ → Aff (λ _ → x)
const-Aff x x<ε₀ = 1 , x , ≤-S ≤-Z , x<ε₀ ,
  (λ b → transport (x ≤_) ((Z-left-unit (b ⊕ x)) ⁻¹) (⊕-increasing-left b x))

\end{code}

A constant added on the *left* is affine — this is the recursor's partial
application `λ ν → C ⊕ ν` (`C ⊕ ν ≤ (ν ⊕ C) ⊗ ι[2]`).

\begin{code}

const-left-bound : (C ν : 𝓑) → (C ⊕ ν) ≤ ((ν ⊕ C) ⊗ ι[ 2 ])
const-left-bound C ν =
 transport ((C ⊕ ν) ≤_) ((ap (_⊕ (ν ⊕ C)) (Z-left-unit (ν ⊕ C))) ⁻¹)
           (≤-trans step1 step2)
 where
  step1 : (C ⊕ ν) ≤ ((ν ⊕ C) ⊕ ν)
  step1 = transport ((C ⊕ ν) ≤_) ((⊕-assoc ν C ν) ⁻¹)
                    (⊕-increasing-left ν (C ⊕ ν))

  step2 : ((ν ⊕ C) ⊕ ν) ≤ ((ν ⊕ C) ⊕ (ν ⊕ C))
  step2 = ⊕-mono-right (ν ⊕ C) (⊕-increasing-right ν C)

const-left-Aff : (C : 𝓑) → C < ε₀ → Aff (λ ν → C ⊕ ν)
const-left-Aff C C<ε₀ = 2 , C , ≤-S ≤-Z , C<ε₀ , const-left-bound C

\end{code}

The affine class is closed under composition — the key step that lets the
combinators `K, S` build affine functions without right distributivity.

\begin{code}

Aff-∘ : {φ ψ : 𝓑 → 𝓑} → Aff φ → Aff ψ → Aff (λ b → φ (ψ b))
Aff-∘ {φ} {ψ} (m , d , m+ , d<ε₀ , fb) (n , e , n+ , e<ε₀ , gb) =
 (n ·ℕ m) , (e ⊕ d) , nm+ , ⊕-<-ε₀ e d e<ε₀ d<ε₀ , bound
 where
  nm+ : S Z ≤ ι[ n ·ℕ m ]
  nm+ = transport (S Z ≤_) (ι-*-homo n m) (one-≤-⊗ ι[ n ] ι[ m ] n+ m+)

  bound : (b : 𝓑) → φ (ψ b) ≤ ((b ⊕ (e ⊕ d)) ⊗ ι[ n ·ℕ m ])
  bound b = transport (λ z → φ (ψ b) ≤ (z ⊗ ι[ n ·ℕ m ])) (⊕-assoc b e d) chain
   where
    inner : (ψ b ⊕ d) ≤ (((b ⊕ e) ⊕ d) ⊗ ι[ n ])
    inner = ≤-trans (⊕-mono-left (gb b) d) (affine-fold-num (b ⊕ e) d n n+)

    assoc-eq : ((((b ⊕ e) ⊕ d) ⊗ ι[ n ]) ⊗ ι[ m ])
             ＝ (((b ⊕ e) ⊕ d) ⊗ ι[ n ·ℕ m ])
    assoc-eq = ⊗-assoc ((b ⊕ e) ⊕ d) ι[ n ] ι[ m ]
             ∙ ap (((b ⊕ e) ⊕ d) ⊗_) (ι-*-homo n m)

    chain : φ (ψ b) ≤ (((b ⊕ e) ⊕ d) ⊗ ι[ n ·ℕ m ])
    chain = transport (λ z → φ (ψ b) ≤ z) assoc-eq
                      (≤-trans (fb (ψ b)) (⊗-mono-left inner ι[ m ]))

\end{code}

The affine class is closed under pointwise sum: each summand is raised to the
common multiplier `ι[m·n]`, and the sum doubles it to `ι[(m·n)·2]`.

\begin{code}

Aff-⊕ : {φ ψ : 𝓑 → 𝓑} → Aff φ → Aff ψ → Aff (λ a → φ a ⊕ ψ a)
Aff-⊕ {φ} {ψ} (m , d , m+ , d<ε₀ , fb) (n , e , n+ , e<ε₀ , gb) =
 ((m ·ℕ n) ·ℕ 2) , (d ⊕ e) , mn2+ , ⊕-<-ε₀ d e d<ε₀ e<ε₀ , bound
 where
  mn+ : S Z ≤ ι[ m ·ℕ n ]
  mn+ = transport (S Z ≤_) (ι-*-homo m n) (one-≤-⊗ ι[ m ] ι[ n ] m+ n+)

  mn2+ : S Z ≤ ι[ (m ·ℕ n) ·ℕ 2 ]
  mn2+ = transport (S Z ≤_) (ι-*-homo (m ·ℕ n) 2)
                   (one-≤-⊗ ι[ m ·ℕ n ] ι[ 2 ] mn+ (≤-S ≤-Z))

  bound : (a : 𝓑) → (φ a ⊕ ψ a) ≤ ((a ⊕ (d ⊕ e)) ⊗ ι[ (m ·ℕ n) ·ℕ 2 ])
  bound a = ≤-trans (≤-trans (⊕-mono-left (b1 a) (ψ a))
                             (⊕-mono-right (Y a) (b2 a)))
                    final
   where
    Y : 𝓑 → 𝓑
    Y a = (a ⊕ (d ⊕ e)) ⊗ ι[ m ·ℕ n ]

    b1 : (a : 𝓑) → φ a ≤ Y a
    b1 a = ≤-trans (fb a)
             (≤-trans (⊗-mono-left (⊕-mono-right a (⊕-increasing-right d e)) ι[ m ])
                      (⊗-mono-right (a ⊕ (d ⊕ e))
                        (transport (ι[ m ] ≤_) (ι-*-homo m n) (x-≤-x⊗ ι[ m ] ι[ n ] n+))))

    b2 : (a : 𝓑) → ψ a ≤ Y a
    b2 a = ≤-trans (gb a)
             (≤-trans (⊗-mono-left (⊕-mono-right a (⊕-increasing-left d e)) ι[ n ])
                      (⊗-mono-right (a ⊕ (d ⊕ e))
                        (transport (ι[ n ] ≤_) (ι-*-homo m n) (y-≤-⊗ ι[ m ] ι[ n ] m+))))

    final : (Y a ⊕ Y a) ≤ ((a ⊕ (d ⊕ e)) ⊗ ι[ (m ·ℕ n) ·ℕ 2 ])
    final = transport (λ z → (Y a ⊕ Y a) ≤ z) eq (≤-refl (Y a ⊕ Y a))
     where
      eq : (Y a ⊕ Y a) ＝ ((a ⊕ (d ⊕ e)) ⊗ ι[ (m ·ℕ n) ·ℕ 2 ])
      eq = (ap (_⊕ Y a) (Z-left-unit (Y a))) ⁻¹
         ∙ ⊗-assoc (a ⊕ (d ⊕ e)) ι[ m ·ℕ n ] ι[ 2 ]
         ∙ ap ((a ⊕ (d ⊕ e)) ⊗_) (ι-*-homo (m ·ℕ n) 2)

\end{code}

The recursor's partial application is affine: iterating an affine `φ` from a
sub-`ε₀` start gives an affine `λ ν → (sup_k φᵏ a) ⊕ ν`.

\begin{code}

Aff-Iter-partial : {φ : 𝓑 → 𝓑} → Aff φ → (a : 𝓑) → a < ε₀
                 → Aff (λ ν → L (λ k → iter φ a k) ⊕ ν)
Aff-Iter-partial {φ} (succ p , d , _ , d<ε₀ , bound) a a<ε₀ =
 const-left-Aff (L (λ k → iter φ a k))
                (affine-orbit-<-ε₀ φ d p bound d<ε₀ a a<ε₀)
Aff-Iter-partial         (zero   , d , () , d<ε₀ , bound) a a<ε₀

\end{code}
