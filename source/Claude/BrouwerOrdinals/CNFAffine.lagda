Affine maps with `ω`-power multipliers below `ε₀`, and their composition
(constructive) — past the `ω^ω` ceiling.

`PolyAffine` built the affine class over `ω`-polynomials: `f b ≤
⟦ shift k pb ⊞ d ⟧`, input scaled by `ω^k` (`k` a *numeral*) plus a constant,
composing via `shift`/`⊞`. That caps at `ω^ω`, because the scalar is a finite
`ω`-power `ω^k`. This module lifts it to **Cantor normal forms** (`CNF`): the
scalar is `ω^⟦m⟧` for `m` an arbitrary CNF, so *any* ordinal `< ε₀` is a
multiplier. A map is `CAff` when

  `f b ≤ ⟦ ωscale m p ⊕c d ⟧`   for every CNF `p` with `b ≤ ⟦ p ⟧`,

where `ωscale m` multiplies by `ω^⟦m⟧` (adds `m` to every exponent) and `⊕c` is
the ordinary CNF sum.

The point: **`CAff` composes.** The `⊗`-fold `(x ⊗ M ⊕ d) ≤ (x ⊕ d) ⊗ M` that
the `Aff` class relied on is *false* for limit multipliers `M`, so the
`⊗`-affine class does not compose at `ω`-powers (the tower wall). Here the bound
is carried as a CNF and composition closes by pure CNF algebra — `ωscale`
distributes over `⊕c`, scalings compose (`ωscale m ∘ ωscale n = ωscale (m ⊕c
n)`), and `⊕c` reassociates — with *no* fold and, notably, *no* commutative
merge (composition is single-threaded; the commutative natural sum is only
needed for the multi-argument joint bound, elsewhere). So affine maps with
multipliers anywhere below `ε₀` compose, reaching `ε₀` — exactly the closure
the type-level tower needs.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.BrouwerOrdinals.CNFAffine
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import Claude.BrouwerOrdinals.Order fe
open import Claude.BrouwerOrdinals.Orbit fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left ; ⊕-assoc ; orbit-sup-≤)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (ω^_ ; _<_ ; ε₀ ; ⊗-mono-left ; ⊗-mono-right ; ω^-mono ; ω^-<-ε₀ ;
        ⊕-mono-right ; ⊕-increasing-right ; ⊕-<-ε₀ ; Z-left-unit ; tower ; tower-<-ε₀)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊗-left-distrib ; ⊗-assoc ; ⊕-increasing-left ; affine-orbit-≤)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (ω^⊗ ; ⊗-<-ε₀)
open import Claude.BrouwerOrdinals.AffineClosure fe using (SZ-⊗ ; Aff)
open import Claude.BrouwerOrdinals.Affine2 fe using (Aff2 ; Aff2-diag)
open import Claude.BrouwerOrdinals.CNF fe

\end{code}

Associativity of the ordinary CNF sum `⊕c` (a plain structural induction).

\begin{code}

⊕c-assoc : (p q r : CNF) → ((p ⊕c q) ⊕c r) ＝ (p ⊕c (q ⊕c r))
⊕c-assoc 𝟎         q r = refl
⊕c-assoc (ω⟨ a ⟩+ b) q r = ap (ω⟨ a ⟩+_) (⊕c-assoc b q r)

\end{code}

Scaling by `ω^⟦m⟧`: add `m` to every exponent. Its denotation is exactly
multiplication by `ω^⟦m⟧` (the CNF analogue of `PolyAffine.shift-pow`), via the
exponent homomorphism `ω^⊗` and left distributivity.

\begin{code}

ωscale : CNF → CNF → CNF
ωscale m 𝟎         = 𝟎
ωscale m (ω⟨ a ⟩+ b) = ω⟨ m ⊕c a ⟩+ ωscale m b

ωscale-⟦⟧ : (m p : CNF) → ⟦ ωscale m p ⟧ ＝ (ω^ ⟦ m ⟧ ⊗ ⟦ p ⟧)
ωscale-⟦⟧ m 𝟎         = refl
ωscale-⟦⟧ m (ω⟨ a ⟩+ b) =
   ap (_⊕ ⟦ ωscale m b ⟧) exp-eq
 ∙ ap ((ω^ ⟦ m ⟧ ⊗ ω^ ⟦ a ⟧) ⊕_) (ωscale-⟦⟧ m b)
 ∙ (⊗-left-distrib (ω^ ⟦ m ⟧) (ω^ ⟦ a ⟧) ⟦ b ⟧) ⁻¹
 where
  exp-eq : ω^ ⟦ m ⊕c a ⟧ ＝ (ω^ ⟦ m ⟧ ⊗ ω^ ⟦ a ⟧)
  exp-eq = ap ω^_ (⊕c-⟦⟧ m a) ∙ (ω^⊗ ⟦ m ⟧ ⟦ a ⟧) ⁻¹

\end{code}

Scaling distributes over `⊕c`, and scalings compose (exponents adding by `⊕c`)
— the two structural facts composition needs.

\begin{code}

ωscale-⊕c : (m p q : CNF) → ωscale m (p ⊕c q) ＝ (ωscale m p ⊕c ωscale m q)
ωscale-⊕c m 𝟎         q = refl
ωscale-⊕c m (ω⟨ a ⟩+ b) q = ap (ω⟨ m ⊕c a ⟩+_) (ωscale-⊕c m b q)

ωscale-ωscale : (m n p : CNF) → ωscale m (ωscale n p) ＝ ωscale (m ⊕c n) p
ωscale-ωscale m n 𝟎         = refl
ωscale-ωscale m n (ω⟨ a ⟩+ b) =
   ap (λ z → ω⟨ z ⟩+ ωscale m (ωscale n b)) ((⊕c-assoc m n a) ⁻¹)
 ∙ ap (ω⟨ (m ⊕c n) ⊕c a ⟩+_) (ωscale-ωscale m n b)

\end{code}

The CNF-affine class.

\begin{code}

CAff : (𝓑 → 𝓑) → 𝓤₀ ̇
CAff f = Σ m ꞉ CNF , Σ d ꞉ CNF ,
           ((b : 𝓑) (p : CNF) → b ≤ ⟦ p ⟧ → f b ≤ ⟦ ωscale m p ⊕c d ⟧)

\end{code}

Identity (`m = d = 𝟎`) and the additive constant `λ b → b ⊕ ⟦ c ⟧`
(`m = 𝟎`, `d = c`) — the base maps. Both use that `ωscale 𝟎` is the identity
(scaling by `ω^Z = 1`).

\begin{code}

ωscale-𝟎 : (p : CNF) → ⟦ ωscale 𝟎 p ⟧ ＝ ⟦ p ⟧
ωscale-𝟎 p = ωscale-⟦⟧ 𝟎 p ∙ SZ-⊗ ⟦ p ⟧

CAff-id : CAff (λ b → b)
CAff-id = 𝟎 , 𝟎 ,
          (λ b p b≤ → transport (b ≤_)
                        ((⊕c-⟦⟧ (ωscale 𝟎 p) 𝟎 ∙ ωscale-𝟎 p) ⁻¹) b≤)

CAff-add : (c : CNF) → CAff (λ b → b ⊕ ⟦ c ⟧)
CAff-add c = 𝟎 , c ,
             (λ b p b≤ → transport (λ z → (b ⊕ ⟦ c ⟧) ≤ z)
                           ((⊕c-⟦⟧ (ωscale 𝟎 p) c ∙ ap (_⊕ ⟦ c ⟧) (ωscale-𝟎 p)) ⁻¹)
                           (⊕-mono-left b≤ ⟦ c ⟧))

\end{code}

Genuine `ω`-power multipliers: `λ b → ω^⟦m⟧ ⊗ b` is `CAff` for *any* CNF `m`
(`d = 𝟎`). So the class contains multiply-by-`ω^α` for every `α < ε₀` — past
the `ω^ω` ceiling of `PolyAffine` (where `α` was a numeral).

\begin{code}

CAff-ωpow : (m : CNF) → CAff (λ b → ω^ ⟦ m ⟧ ⊗ b)
CAff-ωpow m = m , 𝟎 ,
              (λ b p b≤ → transport (λ z → (ω^ ⟦ m ⟧ ⊗ b) ≤ z)
                            ((⊕c-⟦⟧ (ωscale m p) 𝟎 ∙ ωscale-⟦⟧ m p) ⁻¹)
                            (⊗-mono-right (ω^ ⟦ m ⟧) b≤))

\end{code}

The payoff: **`CAff` is closed under composition**, the scalings adding by
`⊕c` and the constant accumulating — by pure CNF algebra, no `⊗`-fold, no
commutative merge. This is the closure the `⊗`-affine class could not give at
`ω`-power multipliers.

\begin{code}

CAff-∘ : {f g : 𝓑 → 𝓑} → CAff f → CAff g → CAff (λ b → f (g b))
CAff-∘ {f} {g} (m , d , hf) (n , e , hg) =
 (m ⊕c n) , (ωscale m e ⊕c d) , bound
 where
  bound : (b : 𝓑) (p : CNF) → b ≤ ⟦ p ⟧
        → f (g b) ≤ ⟦ ωscale (m ⊕c n) p ⊕c (ωscale m e ⊕c d) ⟧
  bound b p b≤ =
   transport (λ z → f (g b) ≤ ⟦ z ⟧) eq
             (hf (g b) (ωscale n p ⊕c e) (hg b p b≤))
   where
    eq : (ωscale m (ωscale n p ⊕c e) ⊕c d)
       ＝ (ωscale (m ⊕c n) p ⊕c (ωscale m e ⊕c d))
    eq = ap (_⊕c d)
            (ωscale-⊕c m (ωscale n p) e
             ∙ ap (_⊕c ωscale m e) (ωscale-ωscale m n p))
       ∙ ⊕c-assoc (ωscale (m ⊕c n) p) (ωscale m e) d

\end{code}

And the closure to `ε₀`: a `CAff` map sends a `< ε₀` input (bounded by a CNF)
to a `< ε₀` output — because the output bound is a CNF, and every CNF is
`< ε₀`. So the whole class stays below `ε₀`, with composition reaching any
multiplier `< ε₀`.

\begin{code}

CAff-<-ε₀ : {f : 𝓑 → 𝓑} → CAff f
          → (b : 𝓑) (p : CNF) → b ≤ ⟦ p ⟧ → f b < ε₀
CAff-<-ε₀ (m , d , hf) b p b≤ =
 ≤-trans (≤-S (hf b p b≤)) (cnf-<-ε₀ (ωscale m p ⊕c d))

\end{code}

The iteration side. Composition closes for a fixed multiplier; *iterating* one
climbs — that is the multiplicative tower step. Here the step multiplies on the
**left** by a fixed `ω^m` (the side `ωscale` produces), the counterpart of
`MultOrbit`'s right-multiplicative engine. The `k`-th iterate is bounded by
`ω^(m ⊗ ι[k]) ⊗ a₀` — the exponent accumulating `m` once per step (via the
exponent homomorphism `ω^⊗` and the `⊕⊗-succ` reordering from `CNF`) — so the
orbit supremum is `ω^(m ⊗ ω) ⊗ a₀`, which is `< ε₀` for `m < ε₀`.

\begin{code}

ω<ε₀ : ω < ε₀
ω<ε₀ = tower-<-ε₀ 0

module _ (a : ℕ → 𝓑) (m : 𝓑) (step : (k : ℕ) → a (succ k) ≤ (ω^ m ⊗ a k))
       where

 left-mult-orbit-≤ : (k : ℕ) → a k ≤ (ω^ (m ⊗ ι[ k ]) ⊗ a 0)
 left-mult-orbit-≤ zero     =
  transport (a 0 ≤_) ((SZ-⊗ (a 0)) ⁻¹) (≤-refl (a 0))
 left-mult-orbit-≤ (succ k) =
  ≤-trans (≤-trans (step k) (⊗-mono-right (ω^ m) (left-mult-orbit-≤ k)))
          (transport (_≤ (ω^ (m ⊗ ι[ succ k ]) ⊗ a 0))
                     (⊗-assoc (ω^ m) (ω^ (m ⊗ ι[ k ])) (a 0))
                     (⊗-mono-left mono' (a 0)))
  where
   mono' : (ω^ m ⊗ ω^ (m ⊗ ι[ k ])) ≤ ω^ (m ⊗ ι[ succ k ])
   mono' = transport (_≤ ω^ (m ⊗ ι[ succ k ])) ((ω^⊗ m (m ⊗ ι[ k ])) ⁻¹)
                     (ω^-mono (⊕⊗-succ m k))

 left-mult-orbit-sup : L a ≤ (ω^ (m ⊗ ω) ⊗ a 0)
 left-mult-orbit-sup =
  ≤-L (λ k → ≤-trans (left-mult-orbit-≤ k)
              (⊗-mono-left (ω^-mono (⊗-mono-right m (≤-L-upper-bound ι[_] k))) (a 0)))

 left-mult-orbit-<-ε₀ : m < ε₀ → a 0 < ε₀ → L a < ε₀
 left-mult-orbit-<-ε₀ m<ε₀ a0<ε₀ =
  ≤-trans (≤-S left-mult-orbit-sup)
          (⊗-<-ε₀ (ω^ (m ⊗ ω)) (a 0)
                  (ω^-<-ε₀ (m ⊗ ω) (⊗-<-ε₀ m ω m<ε₀ ω<ε₀)) a0<ε₀)

\end{code}

In particular, iterating the `CAff` map `λ b → ω^⟦mc⟧ ⊗ b` from a sub-`ε₀`
start has orbit `< ε₀`, for *any* CNF `mc` — the multiplicative tower step at a
multiplier anywhere below `ε₀` (the step holds definitionally, `iter f a₀ (k+1)
= ω^⟦mc⟧ ⊗ iter f a₀ k`).

\begin{code}

CAff-ωpow-orbit-<-ε₀ : (mc : CNF) (a₀ : 𝓑) → a₀ < ε₀
                     → L (iter (λ b → ω^ ⟦ mc ⟧ ⊗ b) a₀) < ε₀
CAff-ωpow-orbit-<-ε₀ mc a₀ a₀<ε₀ =
 left-mult-orbit-<-ε₀ (iter (λ b → ω^ ⟦ mc ⟧ ⊗ b) a₀) ⟦ mc ⟧
                      (λ k → ≤-refl _) (cnf-<-ε₀ mc) a₀<ε₀

\end{code}

Multiplying a CNF by `ω`, staying a CNF — the operation the *additive* recursor
orbit needs (its increment is `c ⊗ ω`). `⟦ c ⟧ ⊗ ω` is `ω^{(top exponent)+1}`;
rather than compute the exact top exponent (which would need canonical forms),
we bound all of `c`'s exponents by their ordinary sum `topexps c`
(`all-exp-topexps`), whence `⟦ c ⟧ ≤ ω^⟦topexps c⟧ ⊗ ι[len c] ≤ ω^{topexps c + 1}`
(`tail-≤`), and `⟦ c ⟧ ⊗ ω ≤ ω^{topexps c + 2} = ⟦ scaleω c ⟧`.

\begin{code}

topexps : CNF → CNF
topexps 𝟎         = 𝟎
topexps (ω⟨ a ⟩+ b) = a ⊕c topexps b

AllExpLeq-mono : (B B′ : 𝓑) → B ≤ B′ → (c : CNF) → AllExpLeq B c → AllExpLeq B′ c
AllExpLeq-mono B B′ B≤ 𝟎         _          = ⋆
AllExpLeq-mono B B′ B≤ (ω⟨ a ⟩+ b) (h , rest) =
 ≤-trans h B≤ , AllExpLeq-mono B B′ B≤ b rest

all-exp-topexps : (c : CNF) → AllExpLeq ⟦ topexps c ⟧ c
all-exp-topexps 𝟎         = ⋆
all-exp-topexps (ω⟨ a ⟩+ b) =
   transport (⟦ a ⟧ ≤_) ((⊕c-⟦⟧ a (topexps b)) ⁻¹)
             (⊕-increasing-right ⟦ a ⟧ ⟦ topexps b ⟧)
 , AllExpLeq-mono ⟦ topexps b ⟧ ⟦ a ⊕c topexps b ⟧
     (transport (⟦ topexps b ⟧ ≤_) ((⊕c-⟦⟧ a (topexps b)) ⁻¹)
                (⊕-increasing-left ⟦ a ⟧ ⟦ topexps b ⟧))
     b (all-exp-topexps b)

scaleω : CNF → CNF
scaleω c = ω⟨ topexps c ⊕c (ω⟨ 𝟎 ⟩+ (ω⟨ 𝟎 ⟩+ 𝟎)) ⟩+ 𝟎

scaleω-bound : (c : CNF) → (⟦ c ⟧ ⊗ ω) ≤ ⟦ scaleω c ⟧
scaleω-bound c =
 transport (λ z → (⟦ c ⟧ ⊗ ω) ≤ z)
   ((ap ω^_ (⊕c-⟦⟧ (topexps c) (ω⟨ 𝟎 ⟩+ (ω⟨ 𝟎 ⟩+ 𝟎)))) ⁻¹) main
 where
  main : (⟦ c ⟧ ⊗ ω) ≤ ω^ (S (S ⟦ topexps c ⟧))
  main = ⊗-mono-left
           (≤-trans (tail-≤ ⟦ topexps c ⟧ c (all-exp-topexps c))
                    (⊗-mono-right (ω^ ⟦ topexps c ⟧)
                                  (≤-L-upper-bound ι[_] (len c)))) ω

\end{code}

The additive class, closed under composition **and iteration** — the shape the
recursor both consumes and produces. `Add f` means `f b ≤ b ⊕ ⟦ c ⟧` for a
fixed CNF constant `c`. The tower obstruction was that no fixed shape was closed
under both consuming and producing a recursor; here the CNF arithmetic resolves
it *for the additive class*: iterating an additive map is additive again, the
constant growing from `c` to `scaleω c` (via the orbit bound `a ⊕ ⟦c⟧ ⊗ ω` and
`scaleω`) — and `scaleω c` is still a CNF, `< ε₀`. So a nested recursor whose
body is additive stays additive; the single-threaded fragment is fully closed
at `ε₀`.

\begin{code}

Add : (𝓑 → 𝓑) → 𝓤₀ ̇
Add f = Σ c ꞉ CNF , ((b : 𝓑) → f b ≤ (b ⊕ ⟦ c ⟧))

Add-id : Add (λ b → b)
Add-id = 𝟎 , (λ b → ≤-refl b)

Add-∘ : {f g : 𝓑 → 𝓑} → Add f → Add g → Add (λ b → f (g b))
Add-∘ {f} {g} (cf , hf) (cg , hg) = (cg ⊕c cf) , bound
 where
  bound : (b : 𝓑) → f (g b) ≤ (b ⊕ ⟦ cg ⊕c cf ⟧)
  bound b =
   transport (f (g b) ≤_) (ap (b ⊕_) ((⊕c-⟦⟧ cg cf) ⁻¹))
     (transport (f (g b) ≤_) (⊕-assoc b ⟦ cg ⟧ ⟦ cf ⟧)
       (≤-trans (hf (g b)) (⊕-mono-left (hg b) ⟦ cf ⟧)))

Add-orbit : {f : 𝓑 → 𝓑} → Add f → Add (λ a → L (λ k → iter f a k))
Add-orbit {f} (c , hf) =
 scaleω c ,
 (λ a → ≤-trans (orbit-sup-≤ (iter f a) ⟦ c ⟧ (λ k → hf (iter f a k)))
                (⊕-mono-right a (scaleω-bound c)))

Add-<-ε₀ : {f : 𝓑 → 𝓑} → Add f → (b : 𝓑) → b < ε₀ → f b < ε₀
Add-<-ε₀ (c , hf) b b<ε₀ =
 ≤-trans (≤-S (hf b)) (⊕-<-ε₀ b ⟦ c ⟧ b<ε₀ (cnf-<-ε₀ c))

\end{code}

Finite multiplicity — toward the multi-argument (`K`/`S`) joint bound. `Add`
handles composition and iteration but not *duplication*: an argument used twice
contributes `⟦p⟧ ⊕ ⟦p⟧`, which no additive constant absorbs. `nmulc k p` is `k`
copies of `p` summed, denoting `≤ ⟦p⟧ ⊗ ι[k]` (`nmulc-≤`, folding by `⊕⊗-succ`);
two copies bound the duplicate `⟦p⟧ ⊕ ⟦p⟧` (`nmulc-dup`). *Caveat, learned in
the proving:* `nmulc` is built on the **ordinary** `⊕c`, which is not
commutative, so `nmulc` does **not** distribute over `⊕c` — it gives a bound but
does not itself compose. The commutative reordering the joint bound's
composition needs is supplied instead by `CNF.common-bound` (a *common exponent
bound* collapses both arguments to `ω^m ⊗ (finite)`, symmetric, no sort). So
duplication is handled two ways — `nmulc-dup` for a same-argument bound,
`common-bound` for the symmetric composable one — and the finite multiplier is
the `ι[k]` in `⟦p⟧ ⊗ ι[k]`.

\begin{code}

nmulc : ℕ → CNF → CNF
nmulc 0        p = 𝟎
nmulc (succ k) p = p ⊕c nmulc k p

nmulc-≤ : (k : ℕ) (p : CNF) → ⟦ nmulc k p ⟧ ≤ (⟦ p ⟧ ⊗ ι[ k ])
nmulc-≤ zero     p = ≤-Z
nmulc-≤ (succ k) p =
 transport (_≤ (⟦ p ⟧ ⊗ ι[ succ k ])) ((⊕c-⟦⟧ p (nmulc k p)) ⁻¹)
   (≤-trans (⊕-mono-right ⟦ p ⟧ (nmulc-≤ k p)) (⊕⊗-succ ⟦ p ⟧ k))

nmulc-dup : (p : CNF) → (⟦ p ⟧ ⊕ ⟦ p ⟧) ≤ ⟦ nmulc 2 p ⟧
nmulc-dup p = transport ((⟦ p ⟧ ⊕ ⟦ p ⟧) ≤_) (eq ⁻¹) (≤-refl (⟦ p ⟧ ⊕ ⟦ p ⟧))
 where
  eq : ⟦ nmulc 2 p ⟧ ＝ (⟦ p ⟧ ⊕ ⟦ p ⟧)
  eq = ⊕c-⟦⟧ p (p ⊕c 𝟎) ∙ ap (⟦ p ⟧ ⊕_) (⊕c-⟦⟧ p 𝟎)

\end{code}

The **two-sided** additive class — the shape the hereditary predicate needs at
`ι ⇒ ι`. `Add` (right constant only) does not contain the recursor's partial
application `λ ν → orbit ⊕ ν`, whose constant is on the *left* (`⊕` is not
commutative, and `C ⊕ ν ⊄ ν ⊕ C`). `Add± f` allows a constant on each side,
`f b ≤ (⟦α⟧ ⊕ b) ⊕ ⟦β⟧`, so it contains both the recursor partial
(`Add±-const-left`, `β = 𝟎`) and every right-additive map (`Add-to-Add±`,
`α = 𝟎`). And it **composes** — the two constants accumulate on their
respective sides by `⊕`-associativity — so it is the coherent function-type
shape: recursor partials and oracle/relabel maps live in one class closed under
composition, all `< ε₀`.

\begin{code}

Add± : (𝓑 → 𝓑) → 𝓤₀ ̇
Add± f = Σ α ꞉ CNF , Σ β ꞉ CNF , ((b : 𝓑) → f b ≤ ((⟦ α ⟧ ⊕ b) ⊕ ⟦ β ⟧))

Add±-const-left : (C : CNF) → Add± (λ ν → ⟦ C ⟧ ⊕ ν)
Add±-const-left C = C , 𝟎 , (λ ν → ≤-refl (⟦ C ⟧ ⊕ ν))

Add-to-Add± : {f : 𝓑 → 𝓑} → Add f → Add± f
Add-to-Add± {f} (c , hf) =
 𝟎 , c , (λ b → transport (λ z → f b ≤ (z ⊕ ⟦ c ⟧)) ((Z-left-unit b) ⁻¹) (hf b))

Add±-∘ : {f g : 𝓑 → 𝓑} → Add± f → Add± g → Add± (λ b → f (g b))
Add±-∘ {f} {g} (αf , βf , hf) (αg , βg , hg) =
 (αf ⊕c αg) , (βg ⊕c βf) , bound
 where
  bound : (b : 𝓑)
        → f (g b) ≤ ((⟦ αf ⊕c αg ⟧ ⊕ b) ⊕ ⟦ βg ⊕c βf ⟧)
  bound b = transport (f (g b) ≤_) eq
              (≤-trans (hf (g b)) (⊕-mono-left (⊕-mono-right ⟦ αf ⟧ (hg b)) ⟦ βf ⟧))
   where
    assoc1 : (⟦ αf ⟧ ⊕ ((⟦ αg ⟧ ⊕ b) ⊕ ⟦ βg ⟧))
           ＝ (((⟦ αf ⟧ ⊕ ⟦ αg ⟧) ⊕ b) ⊕ ⟦ βg ⟧)
    assoc1 = (⊕-assoc ⟦ αf ⟧ (⟦ αg ⟧ ⊕ b) ⟦ βg ⟧) ⁻¹
           ∙ ap (_⊕ ⟦ βg ⟧) ((⊕-assoc ⟦ αf ⟧ ⟦ αg ⟧ b) ⁻¹)

    eq : ((⟦ αf ⟧ ⊕ ((⟦ αg ⟧ ⊕ b) ⊕ ⟦ βg ⟧)) ⊕ ⟦ βf ⟧)
       ＝ ((⟦ αf ⊕c αg ⟧ ⊕ b) ⊕ ⟦ βg ⊕c βf ⟧)
    eq = ap (_⊕ ⟦ βf ⟧) assoc1
       ∙ ⊕-assoc ((⟦ αf ⟧ ⊕ ⟦ αg ⟧) ⊕ b) ⟦ βg ⟧ ⟦ βf ⟧
       ∙ ap (λ z → (z ⊕ b) ⊕ (⟦ βg ⟧ ⊕ ⟦ βf ⟧)) ((⊕c-⟦⟧ αf αg) ⁻¹)
       ∙ ap (λ z → (⟦ αf ⊕c αg ⟧ ⊕ b) ⊕ z) ((⊕c-⟦⟧ βg βf) ⁻¹)

Add±-<-ε₀ : {f : 𝓑 → 𝓑} → Add± f → (b : 𝓑) → b < ε₀ → f b < ε₀
Add±-<-ε₀ (α , β , hf) b b<ε₀ =
 ≤-trans (≤-S (hf b))
   (⊕-<-ε₀ (⟦ α ⟧ ⊕ b) ⟦ β ⟧
           (⊕-<-ε₀ ⟦ α ⟧ b (cnf-<-ε₀ α) b<ε₀) (cnf-<-ε₀ β))

\end{code}

`Add±` is closed under **iteration** — the orbit of a two-sided-additive map is
two-sided-additive. The `k`-th iterate accumulates the left constant `k` times
on the left and the right constant `k` times on the right (`⊕⊗-succ` on each
side), so `iter g a k ≤ ((⟦α⟧ ⊗ ι[k]) ⊕ a) ⊕ (⟦β⟧ ⊗ ι[k])`, and the supremum
is `((⟦α⟧ ⊗ ω) ⊕ a) ⊕ (⟦β⟧ ⊗ ω) ≤ (⟦scaleω α⟧ ⊕ a) ⊕ ⟦scaleω β⟧` — `Add±`
again, both constants grown by `scaleω`. So `Add±` is closed under composition
*and* iteration and contains the recursor's partial application: the coherent
`ι ⇒ ι` shape the hereditary predicate needs, resolving the tower's
consume-vs-produce mismatch for two-sided-additive bodies.

\begin{code}

Add±-orbit : {g : 𝓑 → 𝓑} → Add± g → Add± (λ a → L (λ k → iter g a k))
Add±-orbit {g} (α , β , hg) = scaleω α , scaleω β , sup-bound
 where
  orbit-bound : (a : 𝓑) (k : ℕ)
              → iter g a k ≤ (((⟦ α ⟧ ⊗ ι[ k ]) ⊕ a) ⊕ (⟦ β ⟧ ⊗ ι[ k ]))
  orbit-bound a zero     = transport (a ≤_) ((Z-left-unit a) ⁻¹) (≤-refl a)
  orbit-bound a (succ k) =
   ≤-trans (hg (iter g a k))
     (≤-trans (⊕-mono-left (⊕-mono-right ⟦ α ⟧ (orbit-bound a k)) ⟦ β ⟧) final)
   where
    Xk : 𝓑
    Xk = (⟦ α ⟧ ⊕ (⟦ α ⟧ ⊗ ι[ k ])) ⊕ a

    innerEq : (⟦ α ⟧ ⊕ (((⟦ α ⟧ ⊗ ι[ k ]) ⊕ a) ⊕ (⟦ β ⟧ ⊗ ι[ k ])))
            ＝ (Xk ⊕ (⟦ β ⟧ ⊗ ι[ k ]))
    innerEq = (⊕-assoc ⟦ α ⟧ ((⟦ α ⟧ ⊗ ι[ k ]) ⊕ a) (⟦ β ⟧ ⊗ ι[ k ])) ⁻¹
            ∙ ap (_⊕ (⟦ β ⟧ ⊗ ι[ k ])) ((⊕-assoc ⟦ α ⟧ (⟦ α ⟧ ⊗ ι[ k ]) a) ⁻¹)

    finalEq : ((⟦ α ⟧ ⊕ (((⟦ α ⟧ ⊗ ι[ k ]) ⊕ a) ⊕ (⟦ β ⟧ ⊗ ι[ k ]))) ⊕ ⟦ β ⟧)
            ＝ (Xk ⊕ (⟦ β ⟧ ⊗ ι[ succ k ]))
    finalEq = ap (_⊕ ⟦ β ⟧) innerEq
            ∙ ⊕-assoc Xk (⟦ β ⟧ ⊗ ι[ k ]) ⟦ β ⟧

    final : ((⟦ α ⟧ ⊕ (((⟦ α ⟧ ⊗ ι[ k ]) ⊕ a) ⊕ (⟦ β ⟧ ⊗ ι[ k ]))) ⊕ ⟦ β ⟧)
          ≤ (((⟦ α ⟧ ⊗ ι[ succ k ]) ⊕ a) ⊕ (⟦ β ⟧ ⊗ ι[ succ k ]))
    final = transport (λ z → z ≤ (((⟦ α ⟧ ⊗ ι[ succ k ]) ⊕ a) ⊕ (⟦ β ⟧ ⊗ ι[ succ k ])))
                      (finalEq ⁻¹)
              (⊕-mono-left (⊕-mono-left (⊕⊗-succ ⟦ α ⟧ k) a) (⟦ β ⟧ ⊗ ι[ succ k ]))

  sup-bound : (a : 𝓑) → L (λ k → iter g a k) ≤ ((⟦ scaleω α ⟧ ⊕ a) ⊕ ⟦ scaleω β ⟧)
  sup-bound a = ≤-L (λ k → ≤-trans (orbit-bound a k) (termBound k))
   where
    αb : (k : ℕ) → (⟦ α ⟧ ⊗ ι[ k ]) ≤ ⟦ scaleω α ⟧
    αb k = ≤-trans (⊗-mono-right ⟦ α ⟧ (≤-L-upper-bound ι[_] k)) (scaleω-bound α)

    βb : (k : ℕ) → (⟦ β ⟧ ⊗ ι[ k ]) ≤ ⟦ scaleω β ⟧
    βb k = ≤-trans (⊗-mono-right ⟦ β ⟧ (≤-L-upper-bound ι[_] k)) (scaleω-bound β)

    termBound : (k : ℕ)
              → (((⟦ α ⟧ ⊗ ι[ k ]) ⊕ a) ⊕ (⟦ β ⟧ ⊗ ι[ k ]))
                ≤ ((⟦ scaleω α ⟧ ⊕ a) ⊕ ⟦ scaleω β ⟧)
    termBound k = ≤-trans (⊕-mono-left (⊕-mono-left (αb k) a) (⟦ β ⟧ ⊗ ι[ k ]))
                          (⊕-mono-right (⟦ scaleω α ⟧ ⊕ a) (βb k))

\end{code}

Assembling the hereditary recursor case. Applying an `Add±` map to a
CNF-bounded argument gives a CNF-bounded result (`Add±-app`). And — the key
hereditary `Iter` step, which `CNFTransformer`'s abstract transformer could not
take — the recursor's partial application `μ-Iter g x = λ ν → orbit(x) ⊕ ν` is
`Add±`, from `Add±-orbit` (the orbit `L (λ k → iter g x k)` is CNF-bounded at
the fixed start `x`) fed into `Add±-const-left`. So *given `Add±` shape for the
body* `g`, the recursor closes hereditarily — the shape-loss wall is gone; what
remains is only the multi-argument `S`-diagonal (which needs a finite
multiplier `Add±` lacks).

\begin{code}

Add±-app : {f : 𝓑 → 𝓑} → Add± f → (b : 𝓑) (p : CNF) → b ≤ ⟦ p ⟧
         → Σ q ꞉ CNF , f b ≤ ⟦ q ⟧
Add±-app {f} (α , β , hf) b p b≤ =
 ((α ⊕c p) ⊕c β) ,
 transport (f b ≤_)
   (ap (_⊕ ⟦ β ⟧) ((⊕c-⟦⟧ α p) ⁻¹) ∙ (⊕c-⟦⟧ (α ⊕c p) β) ⁻¹)
   (≤-trans (hf b) (⊕-mono-left (⊕-mono-right ⟦ α ⟧ b≤) ⟦ β ⟧))

Add±-Iter-partial : {g : 𝓑 → 𝓑} → Add± g → (x : 𝓑) (px : CNF) → x ≤ ⟦ px ⟧
                  → Add± (λ ν → L (λ k → iter g x k) ⊕ ν)
Add±-Iter-partial {g} hg x px x≤ with Add±-orbit hg
... | (α′ , β′ , horb) = ((α′ ⊕c px) ⊕c β′) , 𝟎 , bound
 where
  orbit≤ : L (λ k → iter g x k) ≤ ⟦ (α′ ⊕c px) ⊕c β′ ⟧
  orbit≤ = transport (L (λ k → iter g x k) ≤_)
             (ap (_⊕ ⟦ β′ ⟧) ((⊕c-⟦⟧ α′ px) ⁻¹) ∙ (⊕c-⟦⟧ (α′ ⊕c px) β′) ⁻¹)
             (≤-trans (horb x) (⊕-mono-left (⊕-mono-right ⟦ α′ ⟧ x≤) ⟦ β′ ⟧))

  bound : (ν : 𝓑)
        → (L (λ k → iter g x k) ⊕ ν) ≤ ((⟦ (α′ ⊕c px) ⊕c β′ ⟧ ⊕ ν) ⊕ ⟦ 𝟎 ⟧)
  bound ν = ⊕-mono-left orbit≤ ν

\end{code}

The duplication frontier. `Add±` closes composition, iteration, application and
the recursor partial — everything *except* an argument used twice (the `S`
diagonal), which needs a finite multiplier. The finite-multiplier affine class
`Aff` (`AffineClosure`) *does* handle duplication (`Affine2.Aff2-diag`) and
composition, but its orbit escapes to an `ω`-multiplier — the reason it did not
iterate. With the CNF bridge that is no longer a ceiling: the orbit of an `Aff`
body is **CNF-bounded**. From `affine-orbit-≤` (`L (λ k → iter φ a k) ≤
(a ⊕ d ⊗ ω) ⊗ ω`), the `< ε₀` constant `d` becomes a CNF (`<ε₀-to-cnf`), `d ⊗ ω`
and the outer `⊗ ω` become `scaleω`, and the whole orbit lands in a single CNF.
So a *duplicating* body, when iterated, stays `< ε₀` with an explicit CNF bound
— the `Aff` (duplication) and CNF-orbit (iteration) sides meeting.

\begin{code}

Aff-orbit-cnf : {φ : 𝓑 → 𝓑} → Aff φ → (a : 𝓑) (p : CNF) → a ≤ ⟦ p ⟧
              → Σ q ꞉ CNF , L (λ k → iter φ a k) ≤ ⟦ q ⟧
Aff-orbit-cnf (zero   , d , () , _ , _)
Aff-orbit-cnf {φ} (succ p′ , d , m+ , d<ε₀ , bd) a p a≤ with <ε₀-to-cnf d d<ε₀
... | (dc , d≤) =
 scaleω (p ⊕c scaleω dc) , ≤-trans (affine-orbit-≤ φ d p′ bd a) final
 where
  dω≤ : (d ⊗ ω) ≤ ⟦ scaleω dc ⟧
  dω≤ = ≤-trans (⊗-mono-left d≤ ω) (scaleω-bound dc)

  step1 : (a ⊕ (d ⊗ ω)) ≤ ⟦ p ⊕c scaleω dc ⟧
  step1 = transport ((a ⊕ (d ⊗ ω)) ≤_) ((⊕c-⟦⟧ p (scaleω dc)) ⁻¹)
            (≤-trans (⊕-mono-left a≤ (d ⊗ ω)) (⊕-mono-right ⟦ p ⟧ dω≤))

  final : ((a ⊕ (d ⊗ ω)) ⊗ ω) ≤ ⟦ scaleω (p ⊕c scaleω dc) ⟧
  final = ≤-trans (⊗-mono-left step1 ω) (scaleω-bound (p ⊕c scaleω dc))

\end{code}

The frontier closed in one statement. A jointly-affine `φ` diagonalised
against an affine `γ` is a *duplicating* single-argument affine body
(`Affine2.Aff2-diag`), and the orbit of a duplicating affine body is
CNF-bounded (`Aff-orbit-cnf` above). Composing the two: **iterating a ground
`S`-diagonal — the one operation the additive/`CAff`/`Add±` classes could not
express (an argument used twice) — stays CNF-bounded, hence `< ε₀`, with an
explicit witness.** This is the finite-multiplier *duplication* and the CNF
*iteration* meeting: the two halves of the wall, joined.

\begin{code}

Sdiag-orbit-cnf : {φ : 𝓑 → 𝓑 → 𝓑} {γ : 𝓑 → 𝓑}
                → Aff2 φ → Aff γ
                → (a : 𝓑) (p : CNF) → a ≤ ⟦ p ⟧
                → Σ q ꞉ CNF , L (λ k → iter (λ b → φ b (γ b)) a k) ≤ ⟦ q ⟧
Sdiag-orbit-cnf A2φ Aγ = Aff-orbit-cnf (Aff2-diag A2φ Aγ)

Sdiag-orbit-<-ε₀ : {φ : 𝓑 → 𝓑 → 𝓑} {γ : 𝓑 → 𝓑}
                 → Aff2 φ → Aff γ
                 → (a : 𝓑) → a < ε₀
                 → L (λ k → iter (λ b → φ b (γ b)) a k) < ε₀
Sdiag-orbit-<-ε₀ {φ} {γ} A2φ Aγ a a<ε₀ with <ε₀-to-cnf a a<ε₀
... | (p , a≤) with Sdiag-orbit-cnf A2φ Aγ a p a≤
...   | (q , orbit≤) = ≤-trans (≤-S orbit≤) (cnf-<-ε₀ q)

\end{code}

The feed-forward — and with it the *tower*, for the duplicating case. The
orbit of one ground `S`-diagonal is CNF-bounded (`Sdiag-orbit-cnf`), and a CNF
bound is exactly the start-hypothesis the *same* lemma consumes. So the output
of one duplicating recursor feeds the start of the next: **finitely-nested
ground `S`-diagonal recursors stay CNF-bounded, hence `< ε₀`.** Each nesting
level is a bounded ordinal cost paid once; the height climbs the tower
`ω, ω^ω, …` one exponentiation per level, and finitely many levels never reach
`ε₀`. Here is the two-level witness — the general `n`-level nesting is the same
threading of CNF bounds (the transformer `<ε₀`-code ↦ `<ε₀`-code composed with
itself).

\begin{code}

Sdiag-nest2 : {φ ψ : 𝓑 → 𝓑 → 𝓑} {γ δ : 𝓑 → 𝓑}
            → Aff2 φ → Aff γ → Aff2 ψ → Aff δ
            → (a : 𝓑) → a < ε₀
            → Σ q ꞉ CNF ,
                L (λ j → iter (λ b → ψ b (δ b))
                              (L (λ k → iter (λ b → φ b (γ b)) a k)) j)
                  ≤ ⟦ q ⟧
Sdiag-nest2 A2φ Aγ A2ψ Aδ a a<ε₀ with <ε₀-to-cnf a a<ε₀
... | (p , a≤) with Sdiag-orbit-cnf A2φ Aγ a p a≤
...   | (qi , inner≤) = Sdiag-orbit-cnf A2ψ Aδ _ qi inner≤

\end{code}
