Design pass (not in the tour, not depended on): pinning the affine-transformer
predicate `BoundT′` / `JAff′`.

`dialogue-tree-height-decoupling.md` argues that the function-middle `S` wall
is dissolved by carrying *genuine-ordinal transformer data* at function-typed
arguments. `MultHereditaryFAffN` already has the type-recursive joint affine
bound `BoundT` — the joint bound `a w ≤ (D w ⊕ c) ⊗ M` accumulating ground
arguments into `D` — but it **collapses to `𝟙` at a function-typed argument**
(`BoundT ((σ₁⇒σ₂)⇒τ) _ = 𝟙`), which is exactly the fn-middle boundary.

This module pins the one change: replace that `𝟙` by a transformer. At a
function argument, `BoundT′` takes the argument's own affine data
`(D₁, c₁, M₁)` and yields the result's bound with data derived exactly as the
machine-checked `AffineTransformerProto.fnmid-S-affine`: the constant adds
(`c ⊕ c₁`) and the argument's multiplier is orbited into the result multiplier
(`M₁ ↦ (M₁ ⊗ ω) ⊗ M`). Everything else is `MultHereditaryFAffN`'s `BoundT`
verbatim.

The purpose here is only to check that this predicate **type-checks** — that
the recursion is well-founded (structural on the type) and the derived data
has the right kinds. The combinator cases (`JAff′-Iter`, `JAff′-S` for the
fn-middle diagonal via `fnmid-S-affine`, `JAff′-app`) are the fundamental
theorem this underpins. The conjecture remains open.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.AffTransformerPredicate
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.BrouwerOrdinals.Order fe using (_≤_ ; _⊕_ ; ≤-trans ; ≤-L)
open import Claude.BrouwerOrdinals.Orbit fe using (ω ; _⊗_ ; ⊕-mono-left)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right ; ⊕-<-ε₀)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; validMult-⊗ ; ω-valid)
open import Claude.DialogueTreeHeight.MultHereditaryF fe
 using (𝕋 ; GoodT)

\end{code}

The transformer joint bound. Ground arguments accumulate into `D` (verbatim
from `MultHereditaryFAffN`); a function argument now carries its affine data
and the result's data is derived (the fn-middle transformer).

\begin{code}

BoundT′ : (τ : type) → 𝕋 τ → (𝓑 → 𝓑) → 𝓑 → 𝓑 → 𝓤₀ ̇
BoundT′ ι                a D c M = (w : 𝓑) → a w ≤ ((D w ⊕ c) ⊗ M)
BoundT′ (ι ⇒ τ)          T D c M =
 (T₁ : 𝓑 → 𝓑) → BoundT′ τ (T T₁) (λ w → D w ⊕ T₁ w) c M
BoundT′ ((σ₁ ⇒ σ₂) ⇒ τ)  T D c M =
 (T₁ : 𝕋 (σ₁ ⇒ σ₂)) (D₁ : 𝓑 → 𝓑) (c₁ M₁ : 𝓑)
 → c₁ < ε₀ → ValidMult M₁
 → BoundT′ (σ₁ ⇒ σ₂) T₁ D₁ c₁ M₁
 → BoundT′ τ (T T₁) D (c₁ ⊕ c) ((M₁ ⊗ ω) ⊗ M)

\end{code}

`JAff′` packages the bound with the side conditions, exactly as `JAff`.

\begin{code}

JAff′ : (τ : type) → 𝕋 τ → 𝓤₀ ̇
JAff′ τ T = Σ D ꞉ (𝓑 → 𝓑) , Σ c ꞉ 𝓑 , Σ M ꞉ 𝓑 ,
               GoodT ι D × (c < ε₀) × ValidMult M × BoundT′ τ T D c M

\end{code}

Sanity: the fn-middle result type `(ι ⇒ ι) ⇒ ι` now has genuine content (the
transformer), not `𝟙` — witnessed by the fact that its unfolding mentions
`BoundT′ (ι ⇒ ι) T₁ D₁ c₁ M₁` (the argument's affine data) and produces
`BoundT′ ι (T T₁) D (c ⊕ c₁) ((M₁ ⊗ ω) ⊗ M)`. The multiplier derivation
`(M₁ ⊗ ω) ⊗ M` is exactly `AffineTransformerProto.fnmid-S-affine`.

\begin{code}

_ : (T : 𝕋 ((ι ⇒ ι) ⇒ ι)) (D : 𝓑 → 𝓑) (c M : 𝓑)
  → BoundT′ ((ι ⇒ ι) ⇒ ι) T D c M
    ＝ ((T₁ : 𝕋 (ι ⇒ ι)) (D₁ : 𝓑 → 𝓑) (c₁ M₁ : 𝓑)
        → c₁ < ε₀ → ValidMult M₁
        → BoundT′ (ι ⇒ ι) T₁ D₁ c₁ M₁
        → ((w : 𝓑) → T T₁ w ≤ ((D w ⊕ (c₁ ⊕ c)) ⊗ ((M₁ ⊗ ω) ⊗ M))))
_ = λ T D c M → refl

\end{code}

The predicate is workable: multiplier-monotonicity, threaded through the new
transformer clause (where the derived multiplier `(M₁ ⊗ ω) ⊗ M` is itself
monotone in `M`). This is the kind of structural lemma the fundamental theorem
runs on, and it exercises all three clauses — including the function-argument
one that used to be `𝟙`.

\begin{code}

BoundT′-mono-M : (τ : type) (T : 𝕋 τ) (D : 𝓑 → 𝓑) (c M M′ : 𝓑)
               → M ≤ M′
               → BoundT′ τ T D c M → BoundT′ τ T D c M′
BoundT′-mono-M ι               a D c M M′ h b =
 λ w → ≤-trans (b w) (⊗-mono-right (D w ⊕ c) h)
BoundT′-mono-M (ι ⇒ τ)         T D c M M′ h b =
 λ T₁ → BoundT′-mono-M τ (T T₁) (λ w → D w ⊕ T₁ w) c M M′ h (b T₁)
BoundT′-mono-M ((σ₁ ⇒ σ₂) ⇒ τ) T D c M M′ h b =
 λ T₁ D₁ c₁ M₁ c₁ε vM₁ bT₁ →
  BoundT′-mono-M τ (T T₁) D (c₁ ⊕ c)
    ((M₁ ⊗ ω) ⊗ M) ((M₁ ⊗ ω) ⊗ M′)
    (⊗-mono-right (M₁ ⊗ ω) h)
    (b T₁ D₁ c₁ M₁ c₁ε vM₁ bT₁)

\end{code}

Monotonicity in the accumulator `D` and the constant `c`, threaded through all
three clauses (companions to `BoundT′-mono-M`). At the transformer clause the
output `D` is unchanged and the output constant is `c₁ ⊕ c`, monotone in `c`.

\begin{code}

BoundT′-mono-D : (τ : type) (T : 𝕋 τ) (D D′ : 𝓑 → 𝓑) (c M : 𝓑)
               → ((w : 𝓑) → D w ≤ D′ w)
               → BoundT′ τ T D c M → BoundT′ τ T D′ c M
BoundT′-mono-D ι               a D D′ c M h b =
 λ w → ≤-trans (b w) (⊗-mono-left (⊕-mono-left (h w) c) M)
BoundT′-mono-D (ι ⇒ τ)         T D D′ c M h b =
 λ T₁ → BoundT′-mono-D τ (T T₁) (λ w → D w ⊕ T₁ w) (λ w → D′ w ⊕ T₁ w) c M
          (λ w → ⊕-mono-left (h w) (T₁ w)) (b T₁)
BoundT′-mono-D ((σ₁ ⇒ σ₂) ⇒ τ) T D D′ c M h b =
 λ T₁ D₁ c₁ M₁ c₁ε vM₁ bT₁ →
  BoundT′-mono-D τ (T T₁) D D′ (c₁ ⊕ c) ((M₁ ⊗ ω) ⊗ M) h
    (b T₁ D₁ c₁ M₁ c₁ε vM₁ bT₁)

BoundT′-mono-c : (τ : type) (T : 𝕋 τ) (D : 𝓑 → 𝓑) (c c′ M : 𝓑)
               → c ≤ c′
               → BoundT′ τ T D c M → BoundT′ τ T D c′ M
BoundT′-mono-c ι               a D c c′ M h b =
 λ w → ≤-trans (b w) (⊗-mono-left (⊕-mono-right (D w) h) M)
BoundT′-mono-c (ι ⇒ τ)         T D c c′ M h b =
 λ T₁ → BoundT′-mono-c τ (T T₁) (λ w → D w ⊕ T₁ w) c c′ M h (b T₁)
BoundT′-mono-c ((σ₁ ⇒ σ₂) ⇒ τ) T D c c′ M h b =
 λ T₁ D₁ c₁ M₁ c₁ε vM₁ bT₁ →
  BoundT′-mono-c τ (T T₁) D (c₁ ⊕ c) (c₁ ⊕ c′) ((M₁ ⊗ ω) ⊗ M)
    (⊕-mono-right c₁ h)
    (b T₁ D₁ c₁ M₁ c₁ε vM₁ bT₁)

\end{code}

The pointwise supremum of a sequence of transformers (`L` taken at the ground
leaves), and the sup-lemma: if every member of the sequence meets a *fixed*
bound `(D , c , M)`, so does their pointwise sup. Both are structural on the
type; the sup-lemma pushes the `L` inward through the arrow clauses and closes
at `ι` with `≤-L`.

\begin{code}

sup-𝕋 : (τ : type) → (ℕ → 𝕋 τ) → 𝕋 τ
sup-𝕋 ι       seq = λ w → L (λ k → seq k w)
sup-𝕋 (σ ⇒ τ) seq = λ x → sup-𝕋 τ (λ k → seq k x)

BoundT′-L : (τ : type) (seq : ℕ → 𝕋 τ) (D : 𝓑 → 𝓑) (c M : 𝓑)
          → ((k : ℕ) → BoundT′ τ (seq k) D c M)
          → BoundT′ τ (sup-𝕋 τ seq) D c M
BoundT′-L ι               seq D c M h = λ w → ≤-L (λ k → h k w)
BoundT′-L (ι ⇒ τ)         seq D c M h =
 λ T₁ → BoundT′-L τ (λ k → seq k T₁) (λ w → D w ⊕ T₁ w) c M (λ k → h k T₁)
BoundT′-L ((σ₁ ⇒ σ₂) ⇒ τ) seq D c M h =
 λ T₁ D₁ c₁ M₁ c₁ε vM₁ bT₁ →
  BoundT′-L τ (λ k → seq k T₁) D (c₁ ⊕ c) ((M₁ ⊗ ω) ⊗ M)
    (λ k → h k T₁ D₁ c₁ M₁ c₁ε vM₁ bT₁)

\end{code}

The decisive case: the **function-middle** `S` diagonal. With the middle type a
function (`ι ⇒ ι`), `S φ γ a = φ a (γ a)` feeds `φ` the *function* value `γ a`.
This is the case that collapsed to `𝟙` in `MultHereditaryFAffN` and that every
`bumpk`-budget route double-counted. Here it is **definitional**: `γ a`'s own
affine data `(λ w → Dγ w ⊕ Ta w , cγ , Mγ)` is exactly what `φ`'s transformer
clause consumes, and the result's data `(Dφ , cφ ⊕ cγ , (Mγ ⊗ ω) ⊗ Mφ)` is the
transformer output — the machine-checked `fnmid-S-affine` composition, with the
argument's multiplier `Mγ` orbited into the result multiplier. No re-basing, no
absorption lemma: the predicate was shaped to make this the identity feed.

Note the argument's accumulator `D₁ = λ w → Dγ w ⊕ Ta w` is passed *without* a
`GoodT` obligation — the diagonal `Ta` is an arbitrary majorant argument, not a
globally `< ε₀`-preserving one, and the transformer bound never reads `D₁`
(it is absorbed into `Mγ ⊗ ω`), so no such obligation is needed.

\begin{code}

JAff′-Sfnmid : (Tφ : 𝕋 (ι ⇒ (ι ⇒ ι) ⇒ ι)) (Tγ : 𝕋 (ι ⇒ (ι ⇒ ι)))
             → JAff′ (ι ⇒ (ι ⇒ ι) ⇒ ι) Tφ → JAff′ (ι ⇒ (ι ⇒ ι)) Tγ
             → JAff′ (ι ⇒ ι) (λ Ta → Tφ Ta (Tγ Ta))
JAff′-Sfnmid Tφ Tγ (Dφ , cφ , Mφ , gDφ , cφε , vMφ , bφ)
                   (Dγ , cγ , Mγ , gDγ , cγε , vMγ , bγ) =
   Dφ , (cγ ⊕ cφ) , ((Mγ ⊗ ω) ⊗ Mφ)
 , gDφ
 , ⊕-<-ε₀ cγ cφ cγε cφε
 , validMult-⊗ (validMult-⊗ vMγ ω-valid) vMφ
 , (λ Ta → bφ Ta (Tγ Ta) (λ w → Dγ w ⊕ Ta w) cγ Mγ cγε vMγ (bγ Ta))

\end{code}
