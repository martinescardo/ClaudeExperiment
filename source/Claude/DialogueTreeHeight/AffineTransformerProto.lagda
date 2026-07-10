PROTOTYPE (not in the tour, not depended on): the arithmetic core of the
genuine-ordinal affine-transformer route to function-middle `S`.

Design note: `dialogue-tree-height-decoupling.md`. The route replaces the
tower's `bumpk`-budget data by *genuine ordinal* affine transformers, with the
recursor's raise supplied by the orbit engines (`AffineOrbit`, `MultOrbit`) as
a real ordinal factor rather than a bump-count.

This module machine-checks the two ordinal facts the route rests on — the ones
whose `bumpk` analogues produced the scaling-invariant deficit in the tower:

* `D-Iter-*-<-ε₀` — the recursor's second-order transformer stays `< ε₀`:
  additive raise `d ⊗ ω` (`m = 1`) and multiplicative raise `ω^(m ⊗ ω)`
  (`m > 1`), the latter being the `< ε₀` content of `MultOrbit`;
* `fnmid-μS-<-ε₀` — the function-middle `μ-S` bound
  `μ-S φ γ a = φ(a)(γ(a)) = D(d_{γa}, m_{γa})
             = c₀ ⊕ c₁ ⊗ d_{γa} ⊕ c₂ ⊗ ω^(m_{γa} ⊗ ω)`
  is `< ε₀` whenever all the constants and the argument's affine data
  `(d_{γa}, m_{γa})` are `< ε₀`.

The point is the contrast: `d_{γa}` occurs **once**, and the whole expression
is a composition of `ε₀`-closed operations (`⊕`, `⊗`, `ω^`), so it closes with
no side condition. The tower produced the *same* quantity written
multiplicatively with a bump-count, forcing the single `d_{γa}` to be paid
twice — an impossible `j₂ ≥ jφ +ℕ jγ`. Here there is nothing to pay twice.

This validates the arithmetic, not the predicate; the hereditary `Aff`
closure and its fundamental theorem over `T₁` are the development this
underpins. The conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.AffineTransformerProto
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import Claude.BrouwerOrdinals.Order fe using (_⊕_ ; _≤_ ; ≤-trans)
open import Claude.BrouwerOrdinals.Orbit fe using (ω ; _⊗_ ; ⊕-mono-left)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ω^_ ; ω^-<-ε₀ ; ⊕-<-ε₀ ; tower-<-ε₀ ;
        ⊕-increasing-right ; ⊗-mono-left)
open import Claude.BrouwerOrdinals.OmegaPoly fe using (⊗-<-ε₀)
open import Claude.BrouwerOrdinals.Affine fe using (⊗-assoc)
open import Claude.BrouwerOrdinals.AffineClosure fe using (x-≤-x⊗)
open import Claude.DialogueTreeHeight.MultHereditaryFAff fe
 using (⊕-dup-≤-⊗ω)

\end{code}

`ω < ε₀`, packaged.

\begin{code}

ω-<-ε₀ : ω < ε₀
ω-<-ε₀ = tower-<-ε₀ 0

\end{code}

The recursor's transformer stays `< ε₀`. Additive raise (`m = 1`):

\begin{code}

D-Iter-add-<-ε₀ : (d : 𝓑) → d < ε₀ → (d ⊗ ω) < ε₀
D-Iter-add-<-ε₀ d dε = ⊗-<-ε₀ d ω dε ω-<-ε₀

\end{code}

Multiplicative raise (`m > 1`) — `ω^(m ⊗ ω)`, the `MultOrbit` factor:

\begin{code}

D-Iter-mult-<-ε₀ : (m : 𝓑) → m < ε₀ → (ω^ (m ⊗ ω)) < ε₀
D-Iter-mult-<-ε₀ m mε = ω^-<-ε₀ (m ⊗ ω) (⊗-<-ε₀ m ω mε ω-<-ε₀)

\end{code}

The function-middle `μ-S` bound closes. `d`, `m` are the *middle value*
`γ a`'s affine data; `c₀, c₁, c₂` are `φ(a)`'s transformer constants.

\begin{code}

fnmid-μS-<-ε₀ : (c₀ c₁ c₂ d m : 𝓑)
              → c₀ < ε₀ → c₁ < ε₀ → c₂ < ε₀ → d < ε₀ → m < ε₀
              → (c₀ ⊕ (c₁ ⊗ d) ⊕ (c₂ ⊗ ω^ (m ⊗ ω))) < ε₀
fnmid-μS-<-ε₀ c₀ c₁ c₂ d m c₀ε c₁ε c₂ε dε mε =
 ⊕-<-ε₀ (c₀ ⊕ (c₁ ⊗ d)) (c₂ ⊗ ω^ (m ⊗ ω))
   (⊕-<-ε₀ c₀ (c₁ ⊗ d) c₀ε (⊗-<-ε₀ c₁ d c₁ε dε))
   (⊗-<-ε₀ c₂ (ω^ (m ⊗ ω)) c₂ε (D-Iter-mult-<-ε₀ m mε))

\end{code}

The **structural** crux: `Aff-S` for the function-middle case. Design F
stopped here — its data was *fixed*, so it could not derive `μ-S φ γ`'s
affine data from `φ`'s transformer and `γ`'s (argument-dependent) data. The
obstacle is that `μ-S φ γ (a) = φ(a)(γ a)` puts the argument `a` in a *nested*
position: `γ a`'s constant is itself affine in `a`, say `(a ⊕ e) ⊗ M`, so the
recursor-shaped `φ` yields `a ⊕ (a ⊕ e) ⊗ M`. The lemma below shows this
collapses back into affine form — the nested `a` absorbs into the
**multiplier** — so `μ-S φ γ` remains affine, hence iterable. This is the step
that decides the whole route.

\begin{code}

nested-a-absorb : (a e M : 𝓑) → S Z ≤ M
                → (a ⊕ (a ⊕ e) ⊗ M) ≤ ((a ⊕ e) ⊗ (M ⊗ ω))
nested-a-absorb a e M M+ =
 transport (λ z → (a ⊕ (a ⊕ e) ⊗ M) ≤ z) (⊗-assoc (a ⊕ e) M ω)
   (≤-trans (⊕-mono-left a≤ ((a ⊕ e) ⊗ M))
            (⊕-dup-≤-⊗ω ((a ⊕ e) ⊗ M)))
 where
  a≤ : a ≤ ((a ⊕ e) ⊗ M)
  a≤ = ≤-trans (⊕-increasing-right a e) (x-≤-x⊗ (a ⊕ e) M M+)

\end{code}

Putting the outer `φ`-multiplier `q` back on: the full function-middle `μ-S`
majorant `(a ⊕ (a ⊕ e) ⊗ M) ⊗ q` (argument-dependent constant `(a⊕e)⊗M` from
`γ`, times `φ`'s multiplier `q`) is dominated by the **affine** form
`(a ⊕ e) ⊗ m′` with `m′ = (M ⊗ ω) ⊗ q` — derived data, still affine in `a`,
`< ε₀` when `M, q < ε₀`. So `μ-S φ γ` is `AffBounded` and can be iterated.

\begin{code}

fnmid-S-affine : (a e M q : 𝓑) → S Z ≤ M
               → ((a ⊕ (a ⊕ e) ⊗ M) ⊗ q) ≤ ((a ⊕ e) ⊗ ((M ⊗ ω) ⊗ q))
fnmid-S-affine a e M q M+ =
 transport (λ z → ((a ⊕ (a ⊕ e) ⊗ M) ⊗ q) ≤ z)
           (⊗-assoc (a ⊕ e) (M ⊗ ω) q)
           (⊗-mono-left (nested-a-absorb a e M M+) q)

\end{code}
