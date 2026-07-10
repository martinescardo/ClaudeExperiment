Design F: the type-indexed higher-order transformer — dissolving the A/B fork.

The A/B duality (`MultHereditary` vs `MultHereditaryB`/`E`) came from a *fixed
quantification order*: a function argument was required good either at the
current weight (ground-`S` closes, recursor does not) or globally (recursor
closes, ground-`S` does not), with `γ a` provably good only at weights `≥ a`.

The resolution: let **every argument carry its own transformer**, one that is
*itself* globally valid (`GoodT`). The transformer of a majorant is type-indexed
(`𝕋 ι = 𝓑 → 𝓑`, `𝕋 (σ ⇒ τ) = 𝕋 σ → 𝕋 τ`) — a functional on transformers — and
the result of an application is the *higher-order application* `T Tg`. Because an
argument's transformer `Ta` is globally valid, feeding `(a , Ta)` to `Good γ`
*at every weight* makes `γ a` globally good with transformer `Tγ Ta` — so the
"good only at weights `≥ a`" obstruction disappears, and the same predicate that
feeds globally (recursor-compatible) also closes ground-`S`.

This module proves the structural core: ground extraction, the base combinators,
application (`Good-app`), and — the case blocked throughout — the **general
ground-`S` diagonal `Good-S-diag` for arbitrary `σ , τ`**, including
function-typed `σ`. The recursor is *not* here: its transformer is the
functional-orbit `T Tg =` (orbit of `Tg`), so closing `Iter` needs `GoodT` to be
closed under that orbit — the arithmetic residual (`MultSquareOrbit` is the
super-linear instance). So Design F moves the whole problem from a structural
wall to transformer-orbit-closure: an ordinal-arithmetic question.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryF
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe using (⊕-mono-left)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; S-<-ε₀ ; ⊕-<-ε₀ ; ⊕-mono-right)
open import Claude.BrouwerOrdinals.AffineClosure fe using (Z<ε₀)
open import Claude.DialogueTreeHeight.Majorant fe using (Maj)

\end{code}

The type-indexed transformer, its validity (a logical relation: valid
transformers map valid to valid; at ground, monotone and `< ε₀`-preserving), and
the bound relation. An argument carries a transformer `Tg` and is bounded by it
*at every weight*; the result uses the higher-order application `T Tg`.

\begin{code}

𝕋 : type → 𝓤₀ ̇
𝕋 ι       = 𝓑 → 𝓑
𝕋 (σ ⇒ τ) = 𝕋 σ → 𝕋 τ

GoodT : (σ : type) → 𝕋 σ → 𝓤₀ ̇
GoodT ι       T = ((w : 𝓑) → w < ε₀ → T w < ε₀)
                × ((w w′ : 𝓑) → w ≤ w′ → T w ≤ T w′)
GoodT (σ ⇒ τ) T = (Tg : 𝕋 σ) → GoodT σ Tg → GoodT τ (T Tg)

Bnd : (σ : type) → 𝓑 → 𝕋 σ → Maj σ → 𝓤₀ ̇
Bnd ι       w T a = a ≤ T w
Bnd (σ ⇒ τ) w T φ = (g : Maj σ) (Tg : 𝕋 σ) → GoodT σ Tg
                  → ((w′ : 𝓑) → Bnd σ w′ Tg g) → Bnd τ w (T Tg) (φ g)

Good : (σ : type) → Maj σ → 𝓤₀ ̇
Good σ φ = Σ T ꞉ 𝕋 σ , GoodT σ T × ((w : 𝓑) → Bnd σ w T φ)

\end{code}

Ground extraction: at `ι`, `Good` gives `< ε₀`.

\begin{code}

Good-ι-to-<ε₀ : (a : 𝓑) → Good ι a → a < ε₀
Good-ι-to-<ε₀ a (T , (Tpres , Tmono) , bnd) =
 ≤-trans (≤-S (bnd Z)) (Tpres Z Z<ε₀)

\end{code}

The base combinators. `Zero ↦` the identity transformer `λ w → w`; `Succ ↦` the
identity *functional* `λ Tg → Tg`; `Ω ↦` post-composition with `S`.

\begin{code}

Good-Zero : Good ι Z
Good-Zero =
 (λ w → w) , ((λ w w<ε₀ → w<ε₀) , (λ w w′ w≤w′ → w≤w′)) , (λ w → ≤-Z)

Good-Succ : Good (ι ⇒ ι) (λ a → a)
Good-Succ =
 (λ Tg → Tg) , (λ Tg gTg → gTg) , (λ w g Tg gTg gg → gg w)

Good-Ω : Good (ι ⇒ ι) (λ a → S a)
Good-Ω =
 (λ Tg w → S (Tg w))
 , (λ Tg (gp , gm) → (λ w w<ε₀ → S-<-ε₀ (Tg w) (gp w w<ε₀))
                   , (λ w w′ w≤w′ → ≤-S (gm w w′ w≤w′)))
 , (λ w g Tg gTg gg → ≤-S (gg w))

\end{code}

Application: the result transformer is the higher-order application `TF TG`, the
argument fed with its own transformer (globally).

\begin{code}

Good-app : (σ τ : type) (F : Maj (σ ⇒ τ)) (G : Maj σ)
         → Good (σ ⇒ τ) F → Good σ G → Good τ (F G)
Good-app σ τ F G (TF , gTF , bF) (TG , gTG , bG) =
 TF TG , gTF TG gTG , (λ w → bF w G TG gTG bG)

\end{code}

`K` and the full `S` combinator close *unconditionally* (no orbit hypothesis),
for arbitrary types — `K` weakens (transformer `λ Ta Tb → Ta`), and `S`'s
transformer is `λ Tφ Tγ Ta → (Tφ Ta) (Tγ Ta)`, with the shared argument `a` fed to
both `φ` and `γ` at every weight. Note `S` here is general in *all* of `ρ σ τ`
(the shared argument may be function-typed), a strict generalisation of
`Good-S-diag`.

\begin{code}

Good-K : {σ τ : type} → Good (σ ⇒ τ ⇒ σ) (λ a b → a)
Good-K =
 (λ Ta Tb → Ta) , (λ Ta gTa Tb gTb → gTa) ,
 (λ w a Ta gTa a-glob b Tb gTb b-glob → a-glob w)

Good-S : {ρ σ τ : type}
       → Good ((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ) (λ φ γ a → φ a (γ a))
Good-S =
 (λ Tφ Tγ Ta → (Tφ Ta) (Tγ Ta))
 , (λ Tφ gTφ Tγ gTγ Ta gTa → (gTφ Ta gTa) (Tγ Ta) (gTγ Ta gTa))
 , (λ w φ Tφ gTφ φ-glob γ Tγ gTγ γ-glob a Ta gTa a-glob →
      φ-glob w a Ta gTa a-glob (γ a) (Tγ Ta) (gTγ Ta gTa)
        (λ w′ → γ-glob w′ a Ta gTa a-glob))

\end{code}

The general ground-`S` diagonal — the case blocked throughout, for *arbitrary*
`σ , τ` (including function-typed `σ`). The shared ground argument `a` carries a
transformer `Ta`; `φ a` and `γ a` are both obtained by feeding `(a , Ta)`, and —
crucially — `γ a` is globally good with transformer `Tγ Ta`, because `Good γ`
holds at *every* weight and takes the same `(a , Ta)`. The diagonal's transformer
is `λ Ta → (Tφ Ta) (Tγ Ta)`.

\begin{code}

Good-S-diag : (σ τ : type) (φ : Maj (ι ⇒ σ ⇒ τ)) (γ : Maj (ι ⇒ σ))
            → Good (ι ⇒ σ ⇒ τ) φ → Good (ι ⇒ σ) γ
            → Good (ι ⇒ τ) (λ a → φ a (γ a))
Good-S-diag σ τ φ γ (Tφ , gTφ , bφ) (Tγ , gTγ , bγ) =
 (λ Ta → (Tφ Ta) (Tγ Ta))
 , (λ Ta gTa → (gTφ Ta gTa) (Tγ Ta) (gTγ Ta gTa))
 , bound
 where
  bound : (w : 𝓑) → Bnd (ι ⇒ τ) w (λ Ta → (Tφ Ta) (Tγ Ta)) (λ a → φ a (γ a))
  bound w a Ta gTa a-glob =
   bφ w a Ta gTa a-glob (γ a) (Tγ Ta) (gTγ Ta gTa)
     (λ w′ → bγ w′ a Ta gTa a-glob)

\end{code}

The recursor. Its transformer is the **functional orbit** `Torbit Tg Ta =
λ w → L (λ k → iter Tg Ta k w)` — the argument's transformer `Tg` iterated on the
start's transformer `Ta`. The pointwise orbit bound `iter g a k ≤ iter Tg Ta k w`
holds by induction (globally, using that `GoodT` is preserved along `Tg`), so the
`Bnd` component closes unconditionally. The only thing needing the transformer to
stay `< ε₀` is the `GoodT` component — so `Good-Iter` takes exactly that
**transformer-orbit-closure** (`orbit-good`) as a hypothesis. This pins the
recursor's entire residual to one arithmetic statement about the base transformer
class (of which `MultSquareOrbit.sq-orbit-<-ε₀` is the super-linear instance).

**Honest caveat — the residual is genuinely a *restricted* class.** `orbit-good`
is **false** for the full `GoodT` above: the exponentiation functional
`Tg T = λ w → ω^ (T w)` is `GoodT (ι ⇒ ι)` (monotone, `< ε₀`-preserving), yet its
orbit from the identity is `Torbit Tg id 1 = sup_k (k-fold ω^) 1 = ε₀`, not
`< ε₀`. So `GoodT` must be cut down to a *sub-exponential*, orbit-closed subclass
`𝕄T ⊂ GoodT` (containing `⊕`, `⊗`, squaring — `MultSquareOrbit` — but excluding
`ω^`) on which `orbit-good` holds, and the base combinators must land in `𝕄T`.
That restriction is the remaining arithmetic; `Good-Iter` is stated over the full
`GoodT` only to expose the reduction cleanly. What is *unconditional* here — the
type-structural reconciliation of ground-`S` and the recursor — is what dissolves
the wall; the surviving task is ordinal arithmetic, not type structure.

\begin{code}

μ-Iter : (𝓑 → 𝓑) → 𝓑 → 𝓑 → 𝓑
μ-Iter g a ν = L (λ k → iter g a k) ⊕ ν

Torbit : 𝕋 (ι ⇒ ι) → 𝕋 ι → 𝕋 ι
Torbit Tg Ta = λ w → L (λ k → iter Tg Ta k w)

GoodT-iter : (Tg : 𝕋 (ι ⇒ ι)) (Ta : 𝕋 ι)
           → GoodT (ι ⇒ ι) Tg → GoodT ι Ta → (k : ℕ) → GoodT ι (iter Tg Ta k)
GoodT-iter Tg Ta gTg gTa zero     = gTa
GoodT-iter Tg Ta gTg gTa (succ k) = gTg (iter Tg Ta k) (GoodT-iter Tg Ta gTg gTa k)

GoodT-⊕ : (T₁ T₂ : 𝓑 → 𝓑) → GoodT ι T₁ → GoodT ι T₂
        → GoodT ι (λ w → T₁ w ⊕ T₂ w)
GoodT-⊕ T₁ T₂ (p₁ , m₁) (p₂ , m₂) =
   (λ w w<ε₀ → ⊕-<-ε₀ (T₁ w) (T₂ w) (p₁ w w<ε₀) (p₂ w w<ε₀))
 , (λ w w′ w≤w′ → ≤-trans (⊕-mono-left (m₁ w w′ w≤w′) (T₂ w))
                          (⊕-mono-right (T₁ w′) (m₂ w w′ w≤w′)))

Good-Iter : ((Tg : 𝕋 (ι ⇒ ι)) (Ta : 𝕋 ι)
              → GoodT (ι ⇒ ι) Tg → GoodT ι Ta → GoodT ι (Torbit Tg Ta))
          → Good ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι) μ-Iter
Good-Iter orbit-good =
 (λ Tg Ta Tν w → Torbit Tg Ta w ⊕ Tν w) , goodT , bnd
 where
  goodT : GoodT ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι) (λ Tg Ta Tν w → Torbit Tg Ta w ⊕ Tν w)
  goodT Tg gTg Ta gTa Tν gTν =
   GoodT-⊕ (Torbit Tg Ta) Tν (orbit-good Tg Ta gTg gTa) gTν

  bnd : (w : 𝓑) → Bnd ((ι ⇒ ι) ⇒ ι ⇒ ι ⇒ ι) w
                      (λ Tg Ta Tν w → Torbit Tg Ta w ⊕ Tν w) μ-Iter
  bnd w g Tg gTg g-glob a Ta gTa a-glob ν Tν gTν ν-glob =
   ≤-trans (⊕-mono-left (≤-L-mono (λ k → orbit-pt k w)) ν)
           (⊕-mono-right (Torbit Tg Ta w) (ν-glob w))
   where
    orbit-pt : (k : ℕ) (w′ : 𝓑) → iter g a k ≤ iter Tg Ta k w′
    orbit-pt zero     w′ = a-glob w′
    orbit-pt (succ k) w′ =
     g-glob w′ (iter g a k) (iter Tg Ta k)
       (GoodT-iter Tg Ta gTg gTa k) (λ w″ → orbit-pt k w″)

\end{code}
