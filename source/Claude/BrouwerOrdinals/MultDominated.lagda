The multiplier-dominated class, and the hereditary recursor closure it unlocks.

Every prior hereditary predicate — `Hereditary` (finite `ι[m]`), `PolyHereditary`
(`⊞`-multiplicity), `PolyTransformer`/`CNFTransformer` (abstract transformer) —
closed application, `K` and higher-`S`, but hit the *same* wall on the fully
hereditary recursor: closing `Iter` needs the predicate on `ι ⇒ ι` functions to
**expose enough shape to iterate**, yet the shapes that composed (abstract
transformer) *dropped* that shape, and the shapes that iterated (finite affine)
were not closed under their own orbit (the `ω`-multiplier escape = the tower).

`MultAffine` broke that: a limit-multiplier body `(b ⊕ c) ⊗ M` iterates
(`mult-affine-orbit-<-ε₀`) and its orbit re-enters the same shape at the raised
multiplier `M ↦ ω^(M ⊗ ω)` (`mbody-orbit-≤`). This module packages that shape as
a predicate

  `MDom φ = Σ M , ValidMult M × Σ c , c < ε₀ × (∀ b → φ b ≤ (b ⊕ c) ⊗ M)`,

a `ValidMult` being a positive, doubling-absorbing, `< ε₀` multiplier (closed
under `⊗` and under the orbit-raise `M ↦ ω^(M ⊗ ω)`). The payoff is **`MDom-orbit`**:
the start-varying recursor majorant `λ a → L (λ k → iter φ a k)` of an `MDom`
body is `MDom` again — the hereditary recursor closure the transformer predicates
could not take, now a two-line consequence of `mbody-orbit-≤` + `iter-dominate`.

Honest scope. `MDom` closes the recursor (`MDom-orbit`), application
(`MDom-app`), and the additive leaves (`MDom-additive`: identity, successor,
oracle-relabel). It does **not** yet close *composition* (`φ ∘ ψ` needs
right-sub-distributivity `(X ⊕ E) ⊗ M ≤ X ⊗ M ⊕ E ⊗ M` and an output-constant
extension `(b ⊕ c) ⊗ M ⊕ D`) nor the ground `S`-diagonal. So this is the
recursor half of the hereditary theorem — the previously-blocked half — with the
composition/`S` half pinned as the explicit residual.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.BrouwerOrdinals.MultDominated
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import Claude.BrouwerOrdinals.Order fe
open import Claude.BrouwerOrdinals.Orbit fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (ω^_ ; _<_ ; ε₀ ; ⊗-mono-left ; ⊕-<-ε₀ ; one-≤-ω^ ; ω^-<-ε₀ ;
        tower-<-ε₀ ; ⊕-mono-right ; ⊕-increasing-right ; Z-left-unit)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊗-assoc ; ⊕-increasing-left)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (⊗-<-ε₀)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (x-≤-x⊗ ; ι<ε₀)
open import Claude.BrouwerOrdinals.MultAffine fe
 using (ιn⊗ω-≤-ω ; ω-pos ; dbl-ω^ ; iter-dominate ; mbody-orbit-≤ ; crux)

\end{code}

A valid multiplier: positive, absorbs doubling, and below `ε₀`. Exactly the data
`MultAffine` needs to iterate `(b ⊕ c) ⊗ M`.

\begin{code}

ValidMult : 𝓑 → 𝓤₀ ̇
ValidMult M = (S Z ≤ M) × ((ι[ 2 ] ⊗ M) ≤ M) × (M < ε₀)

\end{code}

`ω` is valid, and the valid multipliers are closed under `⊗` (composition) and
the orbit-raise `M ↦ ω^(M ⊗ ω)` (iteration). Doubling-absorption of a product is
`ι[2] ⊗ (M ⊗ N) = (ι[2] ⊗ M) ⊗ N ≤ M ⊗ N` (`⊗-assoc` then `⊗-mono-left`), and of
an orbit-raise it is `dbl-ω^`.

\begin{code}

ω-valid : ValidMult ω
ω-valid = ω-pos , ιn⊗ω-≤-ω 2 , tower-<-ε₀ 0

validMult-⊗ : {M N : 𝓑} → ValidMult M → ValidMult N → ValidMult (M ⊗ N)
validMult-⊗ {M} {N} (M+ , Mdbl , M<ε₀) (N+ , Ndbl , N<ε₀) =
   ≤-trans M+ (x-≤-x⊗ M N N+)
 , transport (λ z → z ≤ (M ⊗ N)) (⊗-assoc ι[ 2 ] M N) (⊗-mono-left Mdbl N)
 , ⊗-<-ε₀ M N M<ε₀ N<ε₀

validMult-orbit : {M : 𝓑} → ValidMult M → ValidMult (ω^ (M ⊗ ω))
validMult-orbit {M} (M+ , Mdbl , M<ε₀) =
   one-≤-ω^ (M ⊗ ω)
 , dbl-ω^ M M+
 , ω^-<-ε₀ (M ⊗ ω) (⊗-<-ε₀ M ω M<ε₀ (tower-<-ε₀ 0))

\end{code}

The multiplier-dominated class.

\begin{code}

MDom : (𝓑 → 𝓑) → 𝓤₀ ̇
MDom φ = Σ M ꞉ 𝓑 , ValidMult M
       × (Σ c ꞉ 𝓑 , (c < ε₀) × ((b : 𝓑) → φ b ≤ ((b ⊕ c) ⊗ M)))

\end{code}

The additive leaves: `λ b → b ⊕ D` (identity `D = Z`, successor `D = ι[1]`,
oracle-relabel) is `MDom`, at multiplier `ω` with constant `D` — since
`b ⊕ D ≤ (b ⊕ D) ⊗ ω` (`ω ≥ 1`).

\begin{code}

MDom-additive : (D : 𝓑) → D < ε₀ → MDom (λ b → b ⊕ D)
MDom-additive D D<ε₀ =
 ω , ω-valid , D , D<ε₀ , (λ b → x-≤-x⊗ (b ⊕ D) ω ω-pos)

MDom-id : MDom (λ b → b)
MDom-id = MDom-additive Z (ι<ε₀ 0)

MDom-succ : MDom (λ b → S b)
MDom-succ = MDom-additive ι[ 1 ] (ι<ε₀ 1)

\end{code}

Two further leaves the first-order majorants need. The **constant** map
`λ _ → C` is `MDom` (multiplier `ω`, constant `C`): `C ≤ b ⊕ C ≤ (b ⊕ C) ⊗ ω`.
The **left-additive** map `λ ν → C ⊕ ν` — the shape of the partial recursor
majorant `orbit ⊕ ν`, with the constant on the *left* (so `MDom-additive`, which
puts it on the right, misses it since `⊕` is non-commutative) — is `MDom` too:
`C ⊕ ν ≤ (ν ⊕ C) ⊕ (ν ⊕ C) = (ν ⊕ C) ⊗ ι[2] ≤ (ν ⊕ C) ⊗ ω`.

\begin{code}

MDom-const : (C : 𝓑) → C < ε₀ → MDom (λ _ → C)
MDom-const C C<ε₀ =
 ω , ω-valid , C , C<ε₀ ,
 (λ b → ≤-trans (⊕-increasing-left b C) (x-≤-x⊗ (b ⊕ C) ω ω-pos))

MDom-const-left : (C : 𝓑) → C < ε₀ → MDom (λ ν → C ⊕ ν)
MDom-const-left C C<ε₀ =
 ω , ω-valid , C , C<ε₀ , bound
 where
  bound : (ν : 𝓑) → (C ⊕ ν) ≤ ((ν ⊕ C) ⊗ ω)
  bound ν = ≤-trans step1 (≤-trans step2 step3)
   where
    Y : 𝓑
    Y = ν ⊕ C

    step1 : (C ⊕ ν) ≤ (Y ⊕ Y)
    step1 = ≤-trans (⊕-mono-left (⊕-increasing-left ν C) ν)
                    (⊕-mono-right Y (⊕-increasing-right ν C))

    step2 : (Y ⊕ Y) ≤ (Y ⊗ ι[ 2 ])
    step2 = transport (λ z → (Y ⊕ Y) ≤ z)
                      ((ap (_⊕ Y) (Z-left-unit Y)) ⁻¹) (≤-refl (Y ⊕ Y))

    step3 : (Y ⊗ ι[ 2 ]) ≤ (Y ⊗ ω)
    step3 = ≤-L-upper-bound (λ k → Y ⊗ ι[ k ]) 2

\end{code}

Application: an `MDom` function sends a `< ε₀` argument to a `< ε₀` value —
`φ a ≤ (a ⊕ c) ⊗ M < ε₀`.

\begin{code}

MDom-app : {φ : 𝓑 → 𝓑} → MDom φ → (a : 𝓑) → a < ε₀ → φ a < ε₀
MDom-app {φ} (M , (M+ , dbl , M<ε₀) , c , c<ε₀ , bound) a a<ε₀ =
 ≤-trans (≤-S (bound a))
         (⊗-<-ε₀ (a ⊕ c) M (⊕-<-ε₀ a c a<ε₀ c<ε₀) M<ε₀)

\end{code}

The payoff — the hereditary recursor closure. The start-varying recursor
majorant `λ a → L (λ k → iter φ a k)` of an `MDom` body `φ` is `MDom` again, at
the raised multiplier `ω^(M ⊗ ω)` and the *same* constant `c`: dominate `φ` by
the monotone body `(b ⊕ c) ⊗ M` (`iter-dominate`), then apply `mbody-orbit-≤`.
This is the case the abstract-transformer predicates could not close — here it is
immediate, because the shape survives its own orbit.

\begin{code}

MDom-orbit : {φ : 𝓑 → 𝓑} → MDom φ
           → MDom (λ a → L (λ k → iter φ a k))
MDom-orbit {φ} (M , vM@(M+ , dbl , M<ε₀) , c , c<ε₀ , bound) =
   ω^ (M ⊗ ω)
 , validMult-orbit vM
 , c , c<ε₀
 , newbound
 where
  mb-mono : (b b′ : 𝓑) → b ≤ b′ → ((b ⊕ c) ⊗ M) ≤ ((b′ ⊕ c) ⊗ M)
  mb-mono b b′ b≤b′ = ⊗-mono-left (⊕-mono-left b≤b′ c) M

  newbound : (a : 𝓑) → L (λ k → iter φ a k) ≤ ((a ⊕ c) ⊗ ω^ (M ⊗ ω))
  newbound a = ≤-trans (≤-L-mono (iter-dominate bound mb-mono a))
                       (mbody-orbit-≤ M M+ dbl c a)

\end{code}

Consequently the recursor's orbit stays `< ε₀` for an `MDom` body from a
`< ε₀` start — the recursor half of the first-order fundamental theorem, closed
for the multiplier-dominated shape.

\begin{code}

MDom-orbit-<-ε₀ : {φ : 𝓑 → 𝓑} → MDom φ
                → (a : 𝓑) → a < ε₀ → L (λ k → iter φ a k) < ε₀
MDom-orbit-<-ε₀ hφ a a<ε₀ = MDom-app (MDom-orbit hφ) a a<ε₀

\end{code}

Composition closes — *without* right-sub-distributivity. Naively `φ (ψ b) ≤
((b ⊕ c_ψ) ⊗ M_ψ ⊕ c_φ) ⊗ M_φ`, and pulling `c_φ` out would need the false
`affine-fold`. Instead **enlarge the inner constant** to `c* = c_ψ ⊕ c_φ`: then
`c_φ ≤ c* ≤ (b ⊕ c*) ⊗ M_ψ =: Yᵦ`, so `MultAffine.crux` absorbs it —
`(Yᵦ ⊕ c_φ) ⊗ M_φ ≤ Yᵦ ⊗ M_φ` — and `⊗-assoc` gives `(b ⊕ c*) ⊗ (M_ψ ⊗ M_φ)`.
So the composite is `MDom` at multiplier `M_ψ ⊗ M_φ` (valid, `validMult-⊗`) with
*no* output constant. The `affine-fold` wall is dodged by absorbing the outer
constant into the (enlarged) inner one via `crux`.

\begin{code}

MDom-∘ : {φ ψ : 𝓑 → 𝓑} → MDom φ → MDom ψ → MDom (λ b → φ (ψ b))
MDom-∘ {φ} {ψ} (Mφ , vφ@(Mφ+ , Mφdbl , Mφ<ε₀) , cφ , cφ<ε₀ , bφ)
               (Mψ , vψ@(Mψ+ , Mψdbl , Mψ<ε₀) , cψ , cψ<ε₀ , bψ) =
   Mψ ⊗ Mφ
 , validMult-⊗ vψ vφ
 , (cψ ⊕ cφ) , ⊕-<-ε₀ cψ cφ cψ<ε₀ cφ<ε₀
 , bound
 where
  c* : 𝓑
  c* = cψ ⊕ cφ

  bound : (b : 𝓑) → φ (ψ b) ≤ ((b ⊕ c*) ⊗ (Mψ ⊗ Mφ))
  bound b = transport (λ z → φ (ψ b) ≤ z) (⊗-assoc (b ⊕ c*) Mψ Mφ) chain
   where
    Yb : 𝓑
    Yb = (b ⊕ c*) ⊗ Mψ

    ψb≤Yb : ψ b ≤ Yb
    ψb≤Yb = ≤-trans (bψ b)
              (⊗-mono-left (⊕-mono-right b (⊕-increasing-right cψ cφ)) Mψ)

    cφ≤Yb : cφ ≤ Yb
    cφ≤Yb = ≤-trans (⊕-increasing-left cψ cφ)
              (≤-trans (⊕-increasing-left b c*)
                       (x-≤-x⊗ (b ⊕ c*) Mψ Mψ+))

    step1 : φ (ψ b) ≤ ((Yb ⊕ cφ) ⊗ Mφ)
    step1 = ≤-trans (bφ (ψ b)) (⊗-mono-left (⊕-mono-left ψb≤Yb cφ) Mφ)

    chain : φ (ψ b) ≤ (Yb ⊗ Mφ)
    chain = ≤-trans step1 (crux Mφ Mφ+ Mφdbl Yb cφ cφ≤Yb)

\end{code}

The two-argument, jointly multiplier-dominated class — the common-bound form
(as in `Hereditary`/`Affine2`): both arguments below a common `s`, and the value
below `(s ⊕ c) ⊗ M`. Symmetric in the two arguments, so the `S`-diagonal can feed
either.

\begin{code}

MDom2 : (𝓑 → 𝓑 → 𝓑) → 𝓤₀ ̇
MDom2 F = Σ M ꞉ 𝓑 , ValidMult M
        × (Σ c ꞉ 𝓑 , (c < ε₀)
             × ((s a b : 𝓑) → a ≤ s → b ≤ s → F a b ≤ ((s ⊕ c) ⊗ M)))

\end{code}

The ground `S`-diagonal closes. A jointly-dominated `F` diagonalised against an
`MDom` `G` is `MDom`: take the common bound `s = (x ⊕ c*) ⊗ M_G` with
`c* = c_G ⊕ c` (it dominates `x` and `G x`), feed the joint bound, and absorb the
outer constant `c` with `crux` (as in composition). Result: multiplier
`M_G ⊗ M`, constant `c*`, no output constant. This is the duplication case —
the `S`-combinator's shared argument — closed for the multiplier-dominated shape.

\begin{code}

MDom2-diag : {F : 𝓑 → 𝓑 → 𝓑} {G : 𝓑 → 𝓑}
           → MDom2 F → MDom G → MDom (λ x → F x (G x))
MDom2-diag {F} {G} (M , vM@(M+ , Mdbl , M<ε₀) , c , c<ε₀ , jb)
                   (MG , vG@(MG+ , MGdbl , MG<ε₀) , cG , cG<ε₀ , bG) =
   MG ⊗ M
 , validMult-⊗ vG vM
 , (cG ⊕ c) , ⊕-<-ε₀ cG c cG<ε₀ c<ε₀
 , bound
 where
  c* : 𝓑
  c* = cG ⊕ c

  bound : (x : 𝓑) → F x (G x) ≤ ((x ⊕ c*) ⊗ (MG ⊗ M))
  bound x = transport (λ z → F x (G x) ≤ z) (⊗-assoc (x ⊕ c*) MG M) chain
   where
    s : 𝓑
    s = (x ⊕ c*) ⊗ MG

    x≤s : x ≤ s
    x≤s = ≤-trans (⊕-increasing-right x c*) (x-≤-x⊗ (x ⊕ c*) MG MG+)

    Gx≤s : G x ≤ s
    Gx≤s = ≤-trans (bG x)
             (⊗-mono-left (⊕-mono-right x (⊕-increasing-right cG c)) MG)

    c≤s : c ≤ s
    c≤s = ≤-trans (⊕-increasing-left cG c)
            (≤-trans (⊕-increasing-left x c*) (x-≤-x⊗ (x ⊕ c*) MG MG+))

    chain : F x (G x) ≤ (s ⊗ M)
    chain = ≤-trans (jb s x (G x) x≤s Gx≤s) (crux M M+ Mdbl s c c≤s)

\end{code}

The partial recursor as a two-argument function is jointly dominated. Its
majorant is `F a ν = L (λ k → iter φ a k) ⊕ ν` (orbit from start `a`, plus the
count `ν`). Under a common bound `s` on `a , ν`: the orbit is `≤ (s ⊕ c_φ) ⊗ M′`
(`MDom-orbit`, monotone in the start), and `ν ≤ s ≤ (s ⊕ c_φ) ⊗ M′`, so the sum
is `≤ ((s ⊕ c_φ) ⊗ M′) ⊗ ι[2] = (s ⊕ c_φ) ⊗ (M′ ⊗ ι[2])` — jointly dominated at
multiplier `M′ ⊗ ι[2]` (valid: `ι[2] ⊗ (M′ ⊗ ι[2]) = (ι[2] ⊗ M′) ⊗ ι[2] ≤
M′ ⊗ ι[2]`). Hence the recursor `S`-diagonal `λ x → Iter φ x (G x)` — iterate
`φ` from `x` for `G x` steps — is `MDom`, by `MDom2-diag`.

\begin{code}

ι2-valid-mult : {M′ : 𝓑} → ValidMult M′ → ValidMult (M′ ⊗ ι[ 2 ])
ι2-valid-mult {M′} (M′+ , M′dbl , M′<ε₀) =
   ≤-trans M′+ (x-≤-x⊗ M′ ι[ 2 ] (≤-S ≤-Z))
 , transport (λ z → z ≤ (M′ ⊗ ι[ 2 ])) (⊗-assoc ι[ 2 ] M′ ι[ 2 ])
             (⊗-mono-left M′dbl ι[ 2 ])
 , ⊗-<-ε₀ M′ ι[ 2 ] M′<ε₀ (ι<ε₀ 2)

MDom2-Iter : {φ : 𝓑 → 𝓑} → MDom φ
           → MDom2 (λ a ν → L (λ k → iter φ a k) ⊕ ν)
MDom2-Iter {φ} hφ with MDom-orbit hφ
... | (M′ , vM′@(M′+ , M′dbl , M′<ε₀) , c′ , c′<ε₀ , ob) =
   M′ ⊗ ι[ 2 ]
 , ι2-valid-mult vM′
 , c′ , c′<ε₀
 , jointbound
 where
  jointbound : (s a b : 𝓑) → a ≤ s → b ≤ s
             → (L (λ k → iter φ a k) ⊕ b) ≤ ((s ⊕ c′) ⊗ (M′ ⊗ ι[ 2 ]))
  jointbound s a b a≤s b≤s =
   transport (λ z → (L (λ k → iter φ a k) ⊕ b) ≤ z) AA=final
             (≤-trans (⊕-mono-left orb≤A b) (⊕-mono-right A b≤A))
   where
    A : 𝓑
    A = (s ⊕ c′) ⊗ M′

    orb≤A : L (λ k → iter φ a k) ≤ A
    orb≤A = ≤-trans (ob a) (⊗-mono-left (⊕-mono-left a≤s c′) M′)

    b≤A : b ≤ A
    b≤A = ≤-trans b≤s
            (≤-trans (⊕-increasing-right s c′) (x-≤-x⊗ (s ⊕ c′) M′ M′+))

    AA=final : (A ⊕ A) ＝ ((s ⊕ c′) ⊗ (M′ ⊗ ι[ 2 ]))
    AA=final = (ap (_⊕ A) (Z-left-unit A)) ⁻¹ ∙ ⊗-assoc (s ⊕ c′) M′ ι[ 2 ]

\end{code}

Hence the recursor `S`-diagonal — `λ x → Iter φ x (G x)`, iterate `φ` from `x`
for `G x` steps — is `MDom` for an `MDom` step `φ` and an `MDom` count-map `G`.
This is the start-varying recursor diagonal, the canonical tower-driving term,
now in the multiplier-dominated class (hence composable and iterable further).

\begin{code}

MDom-recursor-diag : {φ : 𝓑 → 𝓑} {G : 𝓑 → 𝓑} → MDom φ → MDom G
                   → MDom (λ x → L (λ k → iter φ x k) ⊕ G x)
MDom-recursor-diag hφ hG = MDom2-diag (MDom2-Iter hφ) hG

\end{code}
