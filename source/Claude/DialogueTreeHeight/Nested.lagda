Attacking (B1): the per-step increment of a nested recursor is *grafting*
(constructive).

The bridge lemma (B) splits (see `Bridge`, `TwoComponent`) into

  **(B1)** the per-step orbit increment of a System T body `f` is `≤ ω^e`
           (the dialogue content), and
  **(B2)** with `e < ε₀` the orbit stays `< ε₀` (done, the orbit engine).

Everywhere so far (B1) is an *assumption*: `Orbit`, `Bridge`, `Conditional`
all take the per-step increment as a hypothesis. This module *proves* (B1) for
the shape that actually drives the tower — a recursor whose body is itself a
recursor iterated on the *variable count*, i.e. the body function

  `f y = kleisli-extension g y`

(grafting a fixed family `g : ℕ → B ℕ` at the leaves of `y`; for a nested
recursor `g = iter h z`, the inner orbit). For such an `f` the per-step
increment is **not assumed but read off the grafting lemma**
`height-kleisli-extension`: grafting adds `b = sup_k height (g k)` *on the
left*, a code fixed *independently of `y`* — the machine-checked form of
"depth cannot see itself", since the grafts `g k` are chosen without seeing
`y`'s depth.

The one new ingredient is the **left-increment orbit engine** (the companion
of `Orbit`'s right-increment engine; `⊕` is non-commutative, so the two are
genuinely different): a fixed *left* increment `b` per step forces the orbit
supremum below `(b ⊗ ω) ⊕ a₀` — one factor of `ω`. With `b = ω^e` this is
`ω^{e+1} ⊕ a₀`: **one `ω`-power per recursor nesting, proven**. The remaining
input is the graft-height bound `height (g k) ≤ ω^e`, which for a nested
recursor is exactly the inner orbit bound — so this converts (B1)'s assumed
increment into the recursive graft bound, grounding the tower step in the
grafting lemma.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.Nested
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Conditional fe
open import Claude.DialogueTreeHeight.Orbit fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left ; ⊕-assoc)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (Z-left-unit ; ⊕-mono-right ; ⊗-mono-right ; ω^_ ; _<_ ; ε₀ ;
        ⊕-<-ε₀ ; S-<-ε₀ ; ω^-<-ε₀ ; tower ; tower-<-ε₀)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (⊗-<-ε₀)

\end{code}

The arithmetic the left-increment step needs: adding one more `b` *on the
left* of `b ⊗ ι[ k ]` is still below `b ⊗ ι[ k+1 ]`. (Over the naturals this
is `b·(1+k) = b·(k+1)`; here it is `≤`, proved by induction, since `⊕` is not
commutative.)

\begin{code}

b⊗-succ-swap : (b : 𝓑) (k : ℕ) → (b ⊕ (b ⊗ ι[ k ])) ≤ (b ⊗ ι[ succ k ])
b⊗-succ-swap b zero     = transport (b ≤_) ((Z-left-unit b) ⁻¹) (≤-refl b)
b⊗-succ-swap b (succ k) =
 transport (_≤ (b ⊗ ι[ succ (succ k) ])) (⊕-assoc b (b ⊗ ι[ k ]) b)
           (⊕-mono-left (b⊗-succ-swap b k) b)

\end{code}

The left-increment orbit engine. Fix an orbit `a : ℕ → 𝓑` with a fixed
per-step *left* increment `b`: `a (k+1) ≤ b ⊕ a k`.

\begin{code}

module _ (a : ℕ → 𝓑) (b : 𝓑)
         (step : (k : ℕ) → a (succ k) ≤ (b ⊕ a k))
       where

 orbit-left-≤ : (k : ℕ) → a k ≤ ((b ⊗ ι[ k ]) ⊕ a 0)
 orbit-left-≤ zero     =
  transport (a 0 ≤_) ((Z-left-unit (a 0)) ⁻¹) (≤-refl (a 0))
 orbit-left-≤ (succ k) =
  ≤-trans (step k)
   (≤-trans (⊕-mono-right b (orbit-left-≤ k))
            (transport (λ z → z ≤ ((b ⊗ ι[ succ k ]) ⊕ a 0))
                       (⊕-assoc b (b ⊗ ι[ k ]) (a 0))
                       (⊕-mono-left (b⊗-succ-swap b k) (a 0))))

 orbit-left-sup-≤ : L a ≤ ((b ⊗ ω) ⊕ a 0)
 orbit-left-sup-≤ =
  ≤-L (λ k → ≤-trans (orbit-left-≤ k)
              (⊕-mono-left (⊗-mono-right b (≤-L-upper-bound ι[_] k)) (a 0)))

 orbit-left-uniform : (k : ℕ) → a k ≤ ((b ⊗ ω) ⊕ a 0)
 orbit-left-uniform k = ≤-trans (≤-L-upper-bound a k) orbit-left-sup-≤

\end{code}

Now the payoff. For a grafting body `f y = kleisli-extension g y`, the
per-step increment `b = sup_k height (g k)` is delivered by the grafting
lemma, so the orbit of heights is uniformly `≤ (b ⊗ ω) ⊕ height x`.

\begin{code}

kleisli-orbit-uniform
 : (g : ℕ → B ℕ) (b : 𝓑) → ((k : ℕ) → height (g k) ≤ b)
 → (x : B ℕ) (k : ℕ)
 → height (iter (λ y → kleisli-extension g y) x k) ≤ ((b ⊗ ω) ⊕ height x)
kleisli-orbit-uniform g b hb x =
 orbit-left-uniform (λ k → height (iter (λ y → kleisli-extension g y) x k)) b step
 where
  step : (k : ℕ)
       → height (iter (λ y → kleisli-extension g y) x (succ k))
         ≤ (b ⊕ height (iter (λ y → kleisli-extension g y) x k))
  step k = height-kleisli-extension g b hb
             (iter (λ y → kleisli-extension g y) x k)

\end{code}

Hence the height of the nested ground iteration `iter' f x n =
kleisli-extension (iter f x) n` (with `f` the grafting body) is bounded by the
orbit sup plus the count height — the recursor case with its increment
*proven*, not assumed.

\begin{code}

height-nested-iter
 : (g : ℕ → B ℕ) (b : 𝓑) → ((k : ℕ) → height (g k) ≤ b)
 → (x n : B ℕ)
 → height (kleisli-extension (iter (λ y → kleisli-extension g y) x) n)
   ≤ (((b ⊗ ω) ⊕ height x) ⊕ height n)
height-nested-iter g b hb x n =
 height-iter-≤-orbit-bound (λ y → kleisli-extension g y) x ((b ⊗ ω) ⊕ height x)
   (kleisli-orbit-uniform g b hb x) n

\end{code}

The tower step, machine-checked. If the graft family has height `≤ ω^e` (for a
nested recursor `g = iter h z`, this is the inner orbit bound), then the nested
iteration has height `< ε₀` — using that `b ⊗ ω = ω^e ⊗ ω = ω^{e+1}`
definitionally, and that `ε₀` is closed under successor, `ω`-exponentiation and
`⊕`. So one recursor nesting costs exactly one `ω`-power on the exponent, and
the climb stays below `ε₀`. This is (B1) *discharged* for the nested-recursor
shape: the per-step increment is the grafting bound `ω^e`, not a hypothesis.

\begin{code}

height-nested-iter-<-ε₀
 : (g : ℕ → B ℕ) (e : 𝓑) → e < ε₀ → ((k : ℕ) → height (g k) ≤ ω^ e)
 → (x n : B ℕ) → height x < ε₀ → height n < ε₀
 → height (kleisli-extension (iter (λ y → kleisli-extension g y) x) n) < ε₀
height-nested-iter-<-ε₀ g e e<ε₀ hb x n hx hn =
 ≤-trans (≤-S (height-nested-iter g (ω^ e) hb x n))
   (⊕-<-ε₀ ((ω^ e ⊗ ω) ⊕ height x) (height n)
           (⊕-<-ε₀ (ω^ e ⊗ ω) (height x)
                   (ω^-<-ε₀ (S e) (S-<-ε₀ e e<ε₀))
                   hx)
           hn)

\end{code}

The tower step **composes** — this is the crucial point for closing the
recursion. Generalise the graft-height bound from `ω^e` to *any* `c < ε₀`. The
uniform orbit bound `(c ⊗ ω) ⊕ height x` is then again `< ε₀` (`ε₀` is closed
under ordinal `⊗` and `⊕`, with `ω < ε₀`), so *every iterate* of a grafting
body whose graft family is uniformly `< ε₀` is bounded by one *single* `< ε₀`
code. Hence that orbit can itself serve as the graft family of an *outer*
nesting, and the construction closes under iteration: grafting bodies with
uniformly-`< ε₀` graft families form a class closed under the nested-recursor
step, uniformly. This is the engine-side hereditary closure.

\begin{code}

ω<ε₀ : ω < ε₀
ω<ε₀ = tower-<-ε₀ 0

nested-orbit-uniform-<-ε₀
 : (g : ℕ → B ℕ) (c : 𝓑) → ((k : ℕ) → height (g k) ≤ c) → c < ε₀
 → (x : B ℕ) → height x < ε₀
 → Σ c′ ꞉ 𝓑 , (c′ < ε₀)
             × ((k : ℕ) → height (iter (λ y → kleisli-extension g y) x k) ≤ c′)
nested-orbit-uniform-<-ε₀ g c hc c<ε₀ x hx =
 ((c ⊗ ω) ⊕ height x) ,
 ⊕-<-ε₀ (c ⊗ ω) (height x) (⊗-<-ε₀ c ω c<ε₀ ω<ε₀) hx ,
 kleisli-orbit-uniform g c hc x

height-nested-iter-<-ε₀-gen
 : (g : ℕ → B ℕ) (c : 𝓑) → ((k : ℕ) → height (g k) ≤ c) → c < ε₀
 → (x n : B ℕ) → height x < ε₀ → height n < ε₀
 → height (kleisli-extension (iter (λ y → kleisli-extension g y) x) n) < ε₀
height-nested-iter-<-ε₀-gen g c hc c<ε₀ x n hx hn =
 ≤-trans (≤-S (height-nested-iter g c hc x n))
   (⊕-<-ε₀ ((c ⊗ ω) ⊕ height x) (height n)
           (⊕-<-ε₀ (c ⊗ ω) (height x) (⊗-<-ε₀ c ω c<ε₀ ω<ε₀) hx)
           hn)

\end{code}

What is proved: the tower step for the nested-recursor shape, with the per-step
increment *established from the grafting lemma* rather than assumed, and — via
the general `< ε₀` graft bound — *closed under its own iteration*
(`nested-orbit-uniform-<-ε₀`), so the recursion closes on the engine side. What
remains open (the residual of (B1)): that a System T body's dialogue
interpretation genuinely has this grafting-body shape hereditarily, with the
graft family the inner orbit — i.e. the syntactic bridge from `⟦ term ⟧` to the
`kleisli-extension g` form, grounding `c` in the magnitude (Howard (A)) via the
Count Lemma. That structural/syntactic step is the remaining dialogue-native
content; the engine now supplies the uniform `< ε₀` closure it needs.

\end{code}
