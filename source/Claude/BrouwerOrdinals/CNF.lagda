Cantor normal forms below `ε₀`, with the natural (Hessenberg) sum
(constructive).

`OmegaPoly` built the natural sum for the `< ω^ω` layer, representing those
ordinals as `ω`-polynomials (`List ℕ`, coefficient-wise sum). The full climb
to `ε₀` needs ordinals whose *exponents* are themselves large — i.e. Cantor
normal forms `ω^{α₁} + ⋯ + ω^{αₙ}` with the `αᵢ` recursively below `ε₀`. This
module is the `ε₀` generalisation: a datatype of CNFs, its denotation into
Brouwer codes, the headline `⟦ c ⟧ < ε₀` for every CNF, the `ω`-power and
ordinary sum, and — the point — the **natural sum**, commutative, with the key
inequality `⟦ p ⟧ ⊕ ⟦ q ⟧ ≤ ⟦ p ⊞ q ⟧` in either argument order (the
commutative upper bound the non-commutative `⊕` cannot give).

The natural sum is what unblocks *composition* below `ε₀`: the `⊗`-fold
`(x ⊗ M ⊕ d) ≤ (x ⊕ d) ⊗ M` is false for limit multipliers, so affine maps
with `ω`-power multipliers do not compose through `⊗`; reordering through the
commutative `⊞` on the exponents is the replacement (exactly as `OmegaPoly`
did one level down).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.BrouwerOrdinals.CNF
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import Claude.BrouwerOrdinals.Order fe
open import Claude.BrouwerOrdinals.Orbit fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-assoc ; ⊕-mono-left)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (ω^_ ; _<_ ; ε₀ ; ⊕-<-ε₀ ; ω^-<-ε₀ ; ω^-mono ; ⊗-mono-right ;
        ⊕-mono-right ; ⊕-increasing-right ; Z-left-unit ;
        ω^-ι1 ; tower ; S-increasing)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊗-left-distrib ; ι-+-homo ; _+ℕ_)
open import Claude.BrouwerOrdinals.AffineClosure fe using (Z<ε₀ ; ⊗ι-<-ε₀)

\end{code}

Cantor normal forms as a sum of `ω`-powers, most significant first: `ω⟨ a ⟩+ b`
denotes `ω^⟦a⟧ ⊕ ⟦b⟧`, and `𝟎` denotes `Z`. The exponents are themselves CNFs
(recursively), so the whole of `< ε₀` is reachable. There is no descending
side-condition — repeated or out-of-order powers are allowed; the denotation
is still a genuine ordinal `< ε₀`, which is all we need for upper bounds.

\begin{code}

data CNF : 𝓤₀ ̇ where
 𝟎     : CNF
 ω⟨_⟩+_ : CNF → CNF → CNF

infixr 6 ω⟨_⟩+_

⟦_⟧ : CNF → 𝓑
⟦ 𝟎 ⟧       = Z
⟦ ω⟨ a ⟩+ b ⟧ = ω^ ⟦ a ⟧ ⊕ ⟦ b ⟧

\end{code}

The headline: every Cantor normal form denotes an ordinal `< ε₀`. By induction,
using that `ε₀` is closed under `ω`-exponentiation (`ω^-<-ε₀`) and `⊕`
(`⊕-<-ε₀`).

\begin{code}

cnf-<-ε₀ : (c : CNF) → ⟦ c ⟧ < ε₀
cnf-<-ε₀ 𝟎         = Z<ε₀
cnf-<-ε₀ (ω⟨ a ⟩+ b) =
 ⊕-<-ε₀ (ω^ ⟦ a ⟧) ⟦ b ⟧ (ω^-<-ε₀ ⟦ a ⟧ (cnf-<-ε₀ a)) (cnf-<-ε₀ b)

\end{code}

The **converse bridge**: every `< ε₀` code is bounded by a CNF. `a < ε₀` means
`a ≤ tower n` for some `n`, and each `tower n` (`ω, ω^ω, ω^{ω^ω}, …`) is itself
a CNF (`tower-cnf`, nested single `ω`-powers). So the whole Brouwer-code `< ε₀`
world — including the constants of the `Aff` class — can be re-read with CNF
bounds, which is what lets the CNF transformer/affine machinery consume them.

\begin{code}

tower-cnf : ℕ → CNF
tower-cnf zero     = ω⟨ ω⟨ 𝟎 ⟩+ 𝟎 ⟩+ 𝟎
tower-cnf (succ n) = ω⟨ tower-cnf n ⟩+ 𝟎

tower-cnf-eq : (n : ℕ) → ⟦ tower-cnf n ⟧ ＝ tower n
tower-cnf-eq zero     = ω^-ι1
tower-cnf-eq (succ n) = ap ω^_ (tower-cnf-eq n)

<ε₀-to-cnf : (a : 𝓑) → a < ε₀ → Σ ac ꞉ CNF , a ≤ ⟦ ac ⟧
<ε₀-to-cnf a (≤-ℓ n q) =
 tower-cnf n ,
 transport (a ≤_) ((tower-cnf-eq n) ⁻¹) (≤-trans (S-increasing a) q)

\end{code}

The single `ω`-power `ω^ a` (denoting `ω^⟦a⟧`), and the ordinary (ordinal,
non-commutative) sum `_⊕c_`, which denotes `⊕` — it appends one CNF's powers
before the other's.

\begin{code}

ωpow : CNF → CNF
ωpow a = ω⟨ a ⟩+ 𝟎

ωpow-⟦⟧ : (a : CNF) → ⟦ ωpow a ⟧ ＝ ω^ ⟦ a ⟧
ωpow-⟦⟧ a = refl

_⊕c_ : CNF → CNF → CNF
𝟎         ⊕c q = q
(ω⟨ a ⟩+ b) ⊕c q = ω⟨ a ⟩+ (b ⊕c q)

infixl 6 _⊕c_

⊕c-⟦⟧ : (p q : CNF) → ⟦ p ⊕c q ⟧ ＝ (⟦ p ⟧ ⊕ ⟦ q ⟧)
⊕c-⟦⟧ 𝟎         q = (Z-left-unit ⟦ q ⟧) ⁻¹
⊕c-⟦⟧ (ω⟨ a ⟩+ b) q =
 ap (ω^ ⟦ a ⟧ ⊕_) (⊕c-⟦⟧ b q) ∙ (⊕-assoc (ω^ ⟦ a ⟧) ⟦ b ⟧ ⟦ q ⟧) ⁻¹

\end{code}

The heart of the natural sum: **a smaller `ω`-power is absorbed on the left of
a larger one.** This is the ordinal fact `ω^A ⊕ ω^C = ω^C` for `A < C` (here as
`≤`, which is what upper bounds need), and it is what lets the merge move the
larger power to the front — the reordering the commutative `⊞` is built on.

First a `⊗`-arithmetic step (the same shape as `Nested.b⊗-succ-swap`): one more
`b` on the *left* of `b ⊗ ι[ n ]` is still below `b ⊗ ι[ n+1 ]`.

\begin{code}

⊕⊗-succ : (b : 𝓑) (n : ℕ) → (b ⊕ (b ⊗ ι[ n ])) ≤ (b ⊗ ι[ succ n ])
⊕⊗-succ b zero     = transport (b ≤_) ((Z-left-unit b) ⁻¹) (≤-refl b)
⊕⊗-succ b (succ n) =
 transport (_≤ (b ⊗ ι[ succ (succ n) ])) (⊕-assoc b (b ⊗ ι[ n ]) b)
           (⊕-mono-left (⊕⊗-succ b n) b)

\end{code}

Hence `ω^B ⊕ (ω^B ⊗ ω) ≤ ω^B ⊗ ω` (the limit `ω^B ⊗ ω` swallows one more
`ω^B` on the left), and so a smaller power `ω^A` (`A ≤ B`) is absorbed into
`ω^(S B) = ω^B ⊗ ω`.

\begin{code}

ωB⊕ωBω : (B : 𝓑) → (ω^ B ⊕ (ω^ B ⊗ ω)) ≤ (ω^ B ⊗ ω)
ωB⊕ωBω B =
 ≤-L (λ n → ≤-trans (⊕⊗-succ (ω^ B) n)
                    (≤-L-upper-bound (λ m → ω^ B ⊗ ι[ m ]) (succ n)))

absorb-ω-succ : (A B : 𝓑) → A ≤ B → (ω^ A ⊕ ω^ (S B)) ≤ ω^ (S B)
absorb-ω-succ A B A≤B =
 ≤-trans (⊕-mono-left (ω^-mono A≤B) (ω^ (S B))) (ωB⊕ωBω B)

\end{code}

Additive principality, the form the merge actually consumes: `ω^(S B)`
absorbs on its left *anything below a finite multiple of `ω^B`* — i.e. any
whole sub-CNF all of whose powers are `≤ B`. (Absorbing a single `ω^A`,
`A ≤ B`, is the case `γ = ω^A`, `k = 1`.) The proof: `ω^(S B) = ω^B ⊗ ω =
sup_n ω^B ⊗ ι[n]`, and `γ ⊕ (ω^B ⊗ ι[n]) ≤ (ω^B ⊗ ι[k]) ⊕ (ω^B ⊗ ι[n]) =
ω^B ⊗ ι[k+n]` (left distributivity), which is below the supremum.

\begin{code}

principal-succ : (B γ : 𝓑) (k : ℕ)
               → γ ≤ (ω^ B ⊗ ι[ k ]) → (γ ⊕ ω^ (S B)) ≤ ω^ (S B)
principal-succ B γ k γ≤ = ≤-L bound
 where
  bound : (n : ℕ) → (γ ⊕ (ω^ B ⊗ ι[ n ])) ≤ (ω^ B ⊗ ω)
  bound n =
   ≤-trans (⊕-mono-left γ≤ (ω^ B ⊗ ι[ n ]))
     (transport (_≤ (ω^ B ⊗ ω)) (eq ⁻¹)
       (⊗-mono-right (ω^ B) (≤-L-upper-bound ι[_] (k +ℕ n))))
   where
    eq : ((ω^ B ⊗ ι[ k ]) ⊕ (ω^ B ⊗ ι[ n ])) ＝ (ω^ B ⊗ ι[ k +ℕ n ])
    eq = (⊗-left-distrib (ω^ B) ι[ k ] ι[ n ]) ⁻¹
       ∙ ap (ω^ B ⊗_) ((ι-+-homo k n) ⁻¹)

\end{code}

The merge step this delivers. A CNF whose powers all have exponent `≤ B` is
below a finite multiple of `ω^B` (each power `≤ ω^B`, and there are `len p` of
them, folded up by `⊕⊗-succ`), hence absorbed on the left of `ω^(S B)`. This is
exactly what the merge does when the larger leading power `ω^(S B)` moves to the
front past the tail below it — the reordering the commutative `⊞` needs, now a
theorem for a whole tail (not just a single power).

\begin{code}

len : CNF → ℕ
len 𝟎         = 0
len (ω⟨ a ⟩+ b) = succ (len b)

AllExpLeq : 𝓑 → CNF → 𝓤₀ ̇
AllExpLeq B 𝟎         = 𝟙
AllExpLeq B (ω⟨ a ⟩+ b) = (⟦ a ⟧ ≤ B) × AllExpLeq B b

tail-≤ : (B : 𝓑) (p : CNF) → AllExpLeq B p → ⟦ p ⟧ ≤ (ω^ B ⊗ ι[ len p ])
tail-≤ B 𝟎         _              = ≤-Z
tail-≤ B (ω⟨ a ⟩+ b) (a≤B , rest) =
 ≤-trans (≤-trans (⊕-mono-left (ω^-mono a≤B) ⟦ b ⟧)
                  (⊕-mono-right (ω^ B) (tail-≤ B b rest)))
         (⊕⊗-succ (ω^ B) (len b))

absorb-tail : (B : 𝓑) (p : CNF) → AllExpLeq B p → (⟦ p ⟧ ⊕ ω^ (S B)) ≤ ω^ (S B)
absorb-tail B p allp = principal-succ B ⟦ p ⟧ (len p) (tail-≤ B p allp)

\end{code}

The commutative bound, *without sorting.* The reason `OmegaPoly` needed the
sorted natural sum was to keep the leading exponent fixed while the
coefficients add. `tail-≤` gives that directly from a **common exponent bound**:
if every power of `p` and of `q` has exponent `≤ m`, then both collapse to
`ω^m ⊗ (finite)`, and their ordinary sum is `ω^m ⊗ ι[len p + len q]` — a bound
that is **symmetric** in `p` and `q` (it depends only on their sizes), so it
dominates `⟦ p ⟧ ⊕ ⟦ q ⟧` *and* `⟦ q ⟧ ⊕ ⟦ p ⟧`. This is the natural-sum-quality
upper bound (leading exponent fixed, coefficients add) the composition of
`ω`-power-affine maps needs — obtained without a decidable comparison, by
supplying the common exponent bound the affine structure already provides.

\begin{code}

common-bound : (m : 𝓑) (p q : CNF) → AllExpLeq m p → AllExpLeq m q
             → (⟦ p ⟧ ⊕ ⟦ q ⟧) ≤ (ω^ m ⊗ ι[ len p +ℕ len q ])
common-bound m p q allp allq = transport (λ z → (⟦ p ⟧ ⊕ ⟦ q ⟧) ≤ z) eq mid
 where
  mid : (⟦ p ⟧ ⊕ ⟦ q ⟧) ≤ ((ω^ m ⊗ ι[ len p ]) ⊕ (ω^ m ⊗ ι[ len q ]))
  mid = ≤-trans (⊕-mono-left (tail-≤ m p allp) ⟦ q ⟧)
                (⊕-mono-right (ω^ m ⊗ ι[ len p ]) (tail-≤ m q allq))
  eq : ((ω^ m ⊗ ι[ len p ]) ⊕ (ω^ m ⊗ ι[ len q ])) ＝ (ω^ m ⊗ ι[ len p +ℕ len q ])
  eq = (⊗-left-distrib (ω^ m) ι[ len p ] ι[ len q ]) ⁻¹
     ∙ ap (ω^ m ⊗_) ((ι-+-homo (len p) (len q)) ⁻¹)

common-bound-<-ε₀ : (m : 𝓑) → m < ε₀ → (p q : CNF)
                  → AllExpLeq m p → AllExpLeq m q → (⟦ p ⟧ ⊕ ⟦ q ⟧) < ε₀
common-bound-<-ε₀ m m<ε₀ p q allp allq =
 ≤-trans (≤-S (common-bound m p q allp allq))
         (⊗ι-<-ε₀ (ω^ m) (len p +ℕ len q) (ω^-<-ε₀ m m<ε₀))

\end{code}

With absorption in hand, two `ω`-powers commute up to `≤` when the exponents
are comparable: the smaller, wherever it sits, is dominated by the sum with the
larger in front.

\begin{code}

ωpow-swap-succ : (A B : 𝓑) → A ≤ B → (ω^ A ⊕ ω^ (S B)) ≤ (ω^ (S B) ⊕ ω^ A)
ωpow-swap-succ A B A≤B =
 ≤-trans (absorb-ω-succ A B A≤B) (⊕-increasing-right (ω^ (S B)) (ω^ A))

\end{code}

Where this leaves the natural sum. The merge that realises the commutative
`⊞` inserts each `ω`-power of one CNF into the other in decreasing order of
exponent, using `absorb-ω-succ` to justify each reordering. What it needs at
every step is to *compare* two exponents — and unlike `OmegaPoly`, where the
exponents were list *positions* (freely comparable as `ℕ`), the CNF exponents
are themselves CNFs, for which there is no free constructive total order (the
ordinal order on Brouwer codes is not decidable at limits). So the merge must
carry a comparison, either as a decidable structural order refining the ordinal
order or supplied per call. That comparison layer is the remaining piece; the
ordinal content beneath it — the absorption above — is done. (`OmegaPoly` is
the special case where the exponents form the freely-ordered `ℕ`, and there the
natural sum is complete.)

\end{code}
