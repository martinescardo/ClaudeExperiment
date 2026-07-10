Natural sum via ω-polynomials (constructive) — the first-order route to `ε₀`.

The affine-closure route hit a provable wall: the fold lemma
`(x ⊗ c) ⊕ d ≤ (x ⊕ d) ⊗ c` is *false* for limit multipliers `c` — e.g.
`(ω ⊗ ω) ⊕ 1 = ω² + 1 > ω² = (ω ⊕ 1) ⊗ ω`. So the constant-inside affine
form does not compose for `ω`-multipliers, and the **Hessenberg natural
(commutative) sum** is genuinely required (Part II's original route).

For the *first-order* fragment the relevant ordinals are `< ω^ω`, i.e.
**ω-polynomials** `c₀ + ω·c₁ + ⋯ + ω^n·cₙ` with natural-number coefficients.
On these, the natural sum is just *coefficient-wise* addition — far simpler
than full Cantor normal forms. This module builds them: the polynomial type,
the natural sum, its commutativity, the Horner denotation into Brouwer codes,
and the key inequality

  `⟦ p ⟧ ⊕ ⟦ q ⟧ ≤ ⟦ p ⊞ q ⟧`   (ordinary sum ≤ natural sum),

which — being symmetric in `p, q` via commutativity of `⊞` — supplies the
commutative upper bound that the affine reordering needs (the lower-degree
terms are absorbed by the higher-degree ones).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.BrouwerOrdinals.OmegaPoly
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import Claude.BrouwerOrdinals.Order fe
open import Claude.BrouwerOrdinals.Orbit fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-assoc ; ⊕-mono-left)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (⊕-mono-right ; ⊕-increasing-right ; S-increasing ; Z-left-unit ;
        ⊗-mono-left ; ⊗-mono-right ; ω^_ ; ω^-mono ; ω^-ι1 ; tower ; tower-strict ;
        tower-<-ε₀ ; _<_ ; ε₀ ; ⊕-<-ε₀ ; tower-double ; tower-mono-ℕ ;
        maxℕ ; ≤ℕ-maxL ; ≤ℕ-maxR)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊗-left-distrib ; ⊗-assoc)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (ι<ε₀ ; Z<ε₀ ; SZ-⊗)

\end{code}

ω-polynomials as little-endian coefficient lists: `[c₀, c₁, …, cₙ]` denotes
`c₀ + ω·c₁ + ⋯ + ω^n·cₙ`.

\begin{code}

data Poly : 𝓤₀ ̇ where
 []  : Poly
 _∷_ : ℕ → Poly → Poly

infixr 5 _∷_

\end{code}

Natural sum: coefficient-wise addition (padding the shorter list).

\begin{code}

_+ℕ_ : ℕ → ℕ → ℕ
m +ℕ zero   = m
m +ℕ succ n = succ (m +ℕ n)

_⊞_ : Poly → Poly → Poly
[]        ⊞ q         = q
(c ∷ cs)  ⊞ []        = c ∷ cs
(c ∷ cs)  ⊞ (d ∷ ds)  = (c +ℕ d) ∷ (cs ⊞ ds)

\end{code}

Commutativity of `⊞`, from commutativity of `+ℕ`.

\begin{code}

zero-+ℕ : (n : ℕ) → (zero +ℕ n) ＝ n
zero-+ℕ zero     = refl
zero-+ℕ (succ n) = ap succ (zero-+ℕ n)

succ-+ℕ : (m n : ℕ) → (succ m +ℕ n) ＝ succ (m +ℕ n)
succ-+ℕ m zero     = refl
succ-+ℕ m (succ n) = ap succ (succ-+ℕ m n)

+ℕ-comm : (m n : ℕ) → (m +ℕ n) ＝ (n +ℕ m)
+ℕ-comm m zero     = (zero-+ℕ m) ⁻¹
+ℕ-comm m (succ n) = ap succ (+ℕ-comm m n) ∙ (succ-+ℕ n m) ⁻¹

⊞-comm : (p q : Poly) → (p ⊞ q) ＝ (q ⊞ p)
⊞-comm []        []        = refl
⊞-comm []        (d ∷ ds)  = refl
⊞-comm (c ∷ cs)  []        = refl
⊞-comm (c ∷ cs)  (d ∷ ds)  =
 ap (_∷ (cs ⊞ ds)) (+ℕ-comm c d) ∙ ap ((d +ℕ c) ∷_) (⊞-comm cs ds)

ι-+ℕ : (m n : ℕ) → ι[ m +ℕ n ] ＝ (ι[ m ] ⊕ ι[ n ])
ι-+ℕ m zero     = refl
ι-+ℕ m (succ n) = ap S (ι-+ℕ m n)

\end{code}

Horner denotation into Brouwer codes: `⟦ c ∷ cs ⟧ = (ω ⊗ ⟦ cs ⟧) ⊕ ι[ c ]`,
giving the descending ordinal `ω^n·cₙ + ⋯ + ω·c₁ + c₀`.

\begin{code}

⟦_⟧ : Poly → 𝓑
⟦ [] ⟧     = Z
⟦ c ∷ cs ⟧ = (ω ⊗ ⟦ cs ⟧) ⊕ ι[ c ]

\end{code}

A finite ordinal commutes past `ω` as an upper bound, and — the key
absorption — past any `ω ⊗ Y` (the finite term is swallowed by the limit on
the left, and re-emerges on the right).

\begin{code}

fin-ω : (c : ℕ) → (ι[ c ] ⊕ ω) ≤ (ω ⊕ ι[ c ])
fin-ω c =
 ≤-L (λ n → ≤-trans
              (transport (_≤ ω) (ι-+ℕ c n) (≤-L-upper-bound ι[_] (c +ℕ n)))
              (⊕-increasing-right ω ι[ c ]))

absorb : (c : ℕ) (Y : 𝓑) → (ι[ c ] ⊕ (ω ⊗ Y)) ≤ ((ω ⊗ Y) ⊕ ι[ c ])
absorb c Z     = transport (ι[ c ] ≤_) ((Z-left-unit ι[ c ]) ⁻¹) (≤-refl ι[ c ])
absorb c (S y) = ≤-trans h1 h2
 where
  A : 𝓑
  A = ω ⊗ y
  h1 : (ι[ c ] ⊕ (A ⊕ ω)) ≤ ((A ⊕ ι[ c ]) ⊕ ω)
  h1 = transport (λ z → z ≤ ((A ⊕ ι[ c ]) ⊕ ω)) (⊕-assoc ι[ c ] A ω)
                 (⊕-mono-left (absorb c y) ω)
  h2 : ((A ⊕ ι[ c ]) ⊕ ω) ≤ ((A ⊕ ω) ⊕ ι[ c ])
  h2 = transport (λ z → z ≤ ((A ⊕ ω) ⊕ ι[ c ])) ((⊕-assoc A ι[ c ] ω) ⁻¹)
         (transport (λ z → (A ⊕ (ι[ c ] ⊕ ω)) ≤ z) ((⊕-assoc A ω ι[ c ]) ⁻¹)
            (⊕-mono-right A (fin-ω c)))
absorb c (L f) =
 ≤-L (λ n → ≤-trans (absorb c (f n))
                    (⊕-mono-left (≤-L-upper-bound (λ k → ω ⊗ f k) n) ι[ c ]))

\end{code}

The key lemma: the ordinary sum of two polynomials is below their natural
sum. By commutativity of `⊞` this holds in either argument order, giving the
symmetric upper bound the affine reordering needs.

\begin{code}

poly-key : (p q : Poly) → (⟦ p ⟧ ⊕ ⟦ q ⟧) ≤ ⟦ p ⊞ q ⟧
poly-key []        q         =
 transport (λ z → z ≤ ⟦ q ⟧) ((Z-left-unit ⟦ q ⟧) ⁻¹) (≤-refl ⟦ q ⟧)
poly-key (c ∷ cs)  []        = ≤-refl ⟦ c ∷ cs ⟧
poly-key (c ∷ cs)  (d ∷ ds)  =
 transport (λ z → (⟦ c ∷ cs ⟧ ⊕ ⟦ d ∷ ds ⟧) ≤ ((ω ⊗ ⟦ cs ⊞ ds ⟧) ⊕ z))
           ((ι-+ℕ c d) ⁻¹) main
 where
  A B C : 𝓑
  A = ω ⊗ ⟦ cs ⟧
  B = ω ⊗ ⟦ ds ⟧
  C = ω ⊗ ⟦ cs ⊞ ds ⟧

  AB≤C : (A ⊕ B) ≤ C
  AB≤C = transport (_≤ C) (⊗-left-distrib ω ⟦ cs ⟧ ⟦ ds ⟧)
                   (⊗-mono-right ω (poly-key cs ds))

  inner : ((ι[ c ] ⊕ B) ⊕ ι[ d ]) ≤ (B ⊕ (ι[ c ] ⊕ ι[ d ]))
  inner = transport (λ z → ((ι[ c ] ⊕ B) ⊕ ι[ d ]) ≤ z) (⊕-assoc B ι[ c ] ι[ d ])
            (⊕-mono-left (absorb c ⟦ ds ⟧) ι[ d ])

  lhs-eq : (⟦ c ∷ cs ⟧ ⊕ ⟦ d ∷ ds ⟧) ＝ (A ⊕ ((ι[ c ] ⊕ B) ⊕ ι[ d ]))
  lhs-eq = ⊕-assoc A ι[ c ] (B ⊕ ι[ d ])
         ∙ ap (A ⊕_) ((⊕-assoc ι[ c ] B ι[ d ]) ⁻¹)

  main : (⟦ c ∷ cs ⟧ ⊕ ⟦ d ∷ ds ⟧) ≤ (C ⊕ (ι[ c ] ⊕ ι[ d ]))
  main = transport (λ z → z ≤ (C ⊕ (ι[ c ] ⊕ ι[ d ]))) (lhs-eq ⁻¹)
           (≤-trans (⊕-mono-right A inner)
             (transport (λ z → z ≤ (C ⊕ (ι[ c ] ⊕ ι[ d ])))
                        (⊕-assoc A B (ι[ c ] ⊕ ι[ d ]))
                        (⊕-mono-left AB≤C (ι[ c ] ⊕ ι[ d ]))))

\end{code}

By commutativity, the natural sum is a *symmetric* upper bound for the
ordinary sum in either order — the commutative bound the affine reordering
needs (and which the non-commutative `⊕` could not provide).

\begin{code}

poly-key' : (p q : Poly) → (⟦ q ⟧ ⊕ ⟦ p ⟧) ≤ ⟦ p ⊞ q ⟧
poly-key' p q =
 transport (λ z → (⟦ q ⟧ ⊕ ⟦ p ⟧) ≤ ⟦ z ⟧) (⊞-comm q p) (poly-key q p)

\end{code}

Every ω-polynomial is `< ε₀`. The crux is `ω ⊗ a < ε₀` for `a < ε₀`, which
uses the exponent homomorphism `ω^a ⊗ ω^b = ω^{a⊕b}` and `1 + β ≤ β + 1`
(so `ω·tower n ≤ tower (n+1)`). Then `⟦ p ⟧ < ε₀` follows by induction. This
makes the natural-sum route actually conclude `< ε₀`, not merely give upper
bounds.

\begin{code}

S⊕≤S : (β : 𝓑) → (S Z ⊕ β) ≤ S β
S⊕≤S Z     = ≤-refl (S Z)
S⊕≤S (S β) = ≤-S (S⊕≤S β)
S⊕≤S (L f) = ≤-L (λ n → ≤-trans (S⊕≤S (f n)) (≤-S (≤-L-upper-bound f n)))

ω^⊗ : (a b : 𝓑) → (ω^ a ⊗ ω^ b) ＝ ω^ (a ⊕ b)
ω^⊗ a Z     = Z-left-unit (ω^ a)
ω^⊗ a (S b) = (⊗-assoc (ω^ a) (ω^ b) ω) ⁻¹ ∙ ap (_⊗ ω) (ω^⊗ a b)
ω^⊗ a (L f) = ap L (dfunext fe (λ n → ω^⊗ a (f n)))

ω⊗tower : (n : ℕ) → (ω ⊗ tower n) ≤ tower (succ n)
ω⊗tower zero =
 transport (λ z → z ≤ tower 1) (eq ⁻¹) (ω^-mono (≤-L-upper-bound ι[_] 2))
 where
  eq : (ω ⊗ ω) ＝ ω^ ι[ 2 ]
  eq = ap (_⊗ ω) ((ω^-ι1) ⁻¹)
     ∙ ap (ω^ ι[ 1 ] ⊗_) ((ω^-ι1) ⁻¹)
     ∙ ω^⊗ ι[ 1 ] ι[ 1 ]
ω⊗tower (succ m) =
 transport (λ z → z ≤ tower (succ (succ m))) (eq ⁻¹)
   (≤-trans (ω^-mono (S⊕≤S (tower m))) (ω^-mono (tower-strict m)))
 where
  eq : (ω ⊗ tower (succ m)) ＝ ω^ (ι[ 1 ] ⊕ tower m)
  eq = ap (_⊗ tower (succ m)) ((ω^-ι1) ⁻¹) ∙ ω^⊗ ι[ 1 ] (tower m)

ω⊗-<-ε₀ : (a : 𝓑) → a < ε₀ → (ω ⊗ a) < ε₀
ω⊗-<-ε₀ a (≤-ℓ n q) =
 ≤-trans
  (≤-S (≤-trans (⊗-mono-right ω (≤-trans (S-increasing a) q)) (ω⊗tower n)))
  (tower-<-ε₀ (succ n))

\end{code}

`ε₀` is closed under ordinal *multiplication*, not just `⊕` and `ω^_`. This is
the multiplicative counterpart of `⊕-<-ε₀`, and it is what the higher-type
climb needs, since the affine height-bounds are `⊗`-based (`(a ⊕ d) ⊗ m`). The
crux is that a tower level squares back into the next: `tower n ⊗ tower n ≤
tower (succ n)`, via the exponent homomorphism `ω^⊗` (`ω^a ⊗ ω^a = ω^(a ⊕ a)`)
and `tower-double` (`tower n ⊕ tower n ≤ tower (succ n)`). Then any two ordinals
`< ε₀` are pushed to a common tower level and their product absorbed one level
up — exactly the shape of `⊕-<-ε₀`.

\begin{code}

tower-sq : (n : ℕ) → (tower n ⊗ tower n) ≤ tower (succ n)
tower-sq zero =
 transport (_≤ tower 1) (eq ⁻¹) (ω^-mono (≤-L-upper-bound ι[_] 2))
 where
  eq : (ω ⊗ ω) ＝ ω^ (ι[ 1 ] ⊕ ι[ 1 ])
  eq = ap (λ z → z ⊗ z) ((ω^-ι1) ⁻¹) ∙ ω^⊗ ι[ 1 ] ι[ 1 ]
tower-sq (succ m) =
 transport (_≤ tower (succ (succ m))) ((ω^⊗ (tower m) (tower m)) ⁻¹)
           (ω^-mono (tower-double m))

⊗-<-ε₀ : (a b : 𝓑) → a < ε₀ → b < ε₀ → (a ⊗ b) < ε₀
⊗-<-ε₀ a b (≤-ℓ j qa) (≤-ℓ j′ qb) =
 ≤-trans (≤-S ab-≤) (tower-<-ε₀ (succ Jm))
 where
  Jm : ℕ
  Jm = maxℕ j j′

  a≤Jm : a ≤ tower Jm
  a≤Jm = ≤-trans (S-increasing a) (≤-trans qa (tower-mono-ℕ j Jm (≤ℕ-maxL j j′)))

  b≤Jm : b ≤ tower Jm
  b≤Jm = ≤-trans (S-increasing b) (≤-trans qb (tower-mono-ℕ j′ Jm (≤ℕ-maxR j j′)))

  ab-≤ : (a ⊗ b) ≤ tower (succ Jm)
  ab-≤ = ≤-trans (≤-trans (⊗-mono-left a≤Jm b) (⊗-mono-right (tower Jm) b≤Jm))
                 (tower-sq Jm)

poly-<-ε₀ : (p : Poly) → ⟦ p ⟧ < ε₀
poly-<-ε₀ []       = Z<ε₀
poly-<-ε₀ (c ∷ cs) =
 ⊕-<-ε₀ (ω ⊗ ⟦ cs ⟧) ι[ c ]
        (ω⊗-<-ε₀ ⟦ cs ⟧ (poly-<-ε₀ cs)) (ι<ε₀ c)

\end{code}

Consequently the natural sum of two ω-polynomials is `< ε₀`, and it is a
*commutative* upper bound for the ordinary sum (in either order). This is the
reordering-and-`< ε₀` package the affine closure needs at `ω^k` multipliers.

\begin{code}

⊞-<-ε₀ : (p q : Poly) → ⟦ p ⊞ q ⟧ < ε₀
⊞-<-ε₀ p q = poly-<-ε₀ (p ⊞ q)

\end{code}

Multiplication by `ω^k`, the missing right-distributing operation. On
ω-polynomials it is just prepending `k` zero coefficients (`shift`), so it
*manifestly* distributes over the coefficient-wise natural sum:

  `shift k (p ⊞ q) = (shift k p) ⊞ (shift k q)`,

and composes by adding exponents (`shift k ∘ shift k′ = shift (k+k′)`). This
is exactly the right distributivity that `affine-fold` lacked for `ω`
(`(ω⊗ω)⊕1 = ω²+1 > ω²`); with `⊞` (commutative sum) and `shift`
(distributing scalar `ω^k`), the affine class `(b ⊞ d)` scaled by `ω^k`
composes cleanly — the unblock for redoing the affine closure with
polynomial majorants.

\begin{code}

shift : ℕ → Poly → Poly
shift zero     p = p
shift (succ k) p = 0 ∷ shift k p

shift-⊞ : (k : ℕ) (p q : Poly) → shift k (p ⊞ q) ＝ ((shift k p) ⊞ (shift k q))
shift-⊞ zero     p q = refl
shift-⊞ (succ k) p q = ap (0 ∷_) (shift-⊞ k p q)

shift-cons0 : (k : ℕ) (Y : Poly) → shift k (0 ∷ Y) ＝ (0 ∷ shift k Y)
shift-cons0 zero     Y = refl
shift-cons0 (succ k) Y = ap (0 ∷_) (shift-cons0 k Y)

shift-shift : (k k′ : ℕ) (p : Poly) → shift k (shift k′ p) ＝ shift (k +ℕ k′) p
shift-shift k zero      p = refl
shift-shift k (succ k′) p =
 shift-cons0 k (shift k′ p) ∙ ap (0 ∷_) (shift-shift k k′ p)

\end{code}

The denotation of a shift is multiplication by `ω^ι[k]` in Brouwer codes —
`⟦ shift k p ⟧ ＝ ω^ι[k] ⊗ ⟦ p ⟧` — the bridge that lets the polynomial
calculus stand in for the `ω^k`-multiplier height bounds. (And it is `< ε₀`,
being a polynomial.)

\begin{code}

ι1⊕ιk : (k : ℕ) → (ι[ 1 ] ⊕ ι[ k ]) ＝ ι[ succ k ]
ι1⊕ιk zero     = refl
ι1⊕ιk (succ k) = ap S (ι1⊕ιk k)

ω-pow-succ : (k : ℕ) → (ω ⊗ ω^ ι[ k ]) ＝ ω^ ι[ succ k ]
ω-pow-succ k =
 ap (_⊗ ω^ ι[ k ]) ((ω^-ι1) ⁻¹) ∙ ω^⊗ ι[ 1 ] ι[ k ] ∙ ap ω^_ (ι1⊕ιk k)

shift-pow : (k : ℕ) (p : Poly) → ⟦ shift k p ⟧ ＝ (ω^ ι[ k ] ⊗ ⟦ p ⟧)
shift-pow zero     p = (SZ-⊗ ⟦ p ⟧) ⁻¹
shift-pow (succ k) p =
 ap (ω ⊗_) (shift-pow k p)
 ∙ ((⊗-assoc ω (ω^ ι[ k ]) ⟦ p ⟧) ⁻¹ ∙ ap (_⊗ ⟦ p ⟧) (ω-pow-succ k))

shift-<-ε₀ : (k : ℕ) (p : Poly) → ⟦ shift k p ⟧ < ε₀
shift-<-ε₀ k p = poly-<-ε₀ (shift k p)

\end{code}

Every ω-polynomial lies below the *fixed* ordinal `ω^ω = tower 1`. The naive
degree bound `⟦p⟧ ≤ ω^ι[length p]` is not provable by direct induction (the
`⊕ ι[c]` overflows), but its *strict* form `S ⟦p⟧ ≤ ω^ι[length p]` is. As a
consequence, any recursively-presented family of ω-polynomials has supremum
`< ε₀` — i.e. a first-order (polynomially-bounded) orbit of heights is bounded
below `ε₀`, uniformly. This is the orbit lemma for the first-order fragment,
read off the polynomial calculus.

\begin{code}

length : Poly → ℕ
length []       = 0
length (c ∷ cs) = succ (length cs)

poly-str : (p : Poly) → S ⟦ p ⟧ ≤ ω^ ι[ length p ]
poly-str []       = ≤-refl (S Z)
poly-str (c ∷ cs) =
 ≤-trans (⊕-mono-right (ω ⊗ ⟦ cs ⟧) (≤-L-upper-bound ι[_] (succ c)))
         (transport (λ z → (ω ⊗ (S ⟦ cs ⟧)) ≤ z) (ω-pow-succ (length cs))
                    (⊗-mono-right ω (poly-str cs)))

poly-≤-tower1 : (p : Poly) → ⟦ p ⟧ ≤ tower 1
poly-≤-tower1 p =
 ≤-trans (S-increasing ⟦ p ⟧)
   (≤-trans (poly-str p) (ω^-mono (≤-L-upper-bound ι[_] (length p))))

poly-family-<-ε₀ : (P : ℕ → Poly) → L (λ j → ⟦ P j ⟧) < ε₀
poly-family-<-ε₀ P =
 ≤-trans (≤-S (≤-L (λ j → poly-≤-tower1 (P j)))) (tower-<-ε₀ 1)

\end{code}
