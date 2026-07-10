The type-level joint zone calculus: the uniform `n`-ary generalization of
`AffBounded` (one ground argument, `MultHereditaryFAff`) and `Aff₂` (two,
`MultHereditaryFAff2`), by recursion on the *type* rather than on an arity.

`BoundT τ T D c M` says the transformer `T : 𝕋 τ` is bounded by a single
multiplied zone: each ground argument passed to `T` is accumulated into the
left summand `D`, and at ground type the value is `≤ ((D w ⊕ c) ⊗ M)`. At a
*function-typed* argument the predicate collapses to `𝟙` — no joint data is
carried across a function argument (that would be Howard's transformer
tower). So the data is substantive exactly on the all-ground prefix of `τ`,
and trivially dischargeable beyond a function argument (`Collapses`,
`BoundT-collapse`). `JAff τ T` packages the bound with the usual side
conditions (`GoodT` summand, constant `< ε₀`, `ValidMult` multiplier).

The lemmas, each the type-level form of an arity-ladder rung:

* `JAff-apply`-style currying is *definitional* (feeding an argument is the
  `BoundT` recursion itself); `JAff-insert` prepends a dead argument
  (`BoundT-mono-D`); `JAff-id/S/const/add/K-outer/Iter` are the combinator
  shapes, generalizing their `Aff`/`Aff₂` versions;
* **`BoundT-absorb`** — the engine: if the accumulated summand `A` is
  dominated by `(B ⊕ c′) ⊗ K`, the whole bound can be re-based from `A` to
  `B`, paying `K ⊕ ι[depth]` in the multiplier (one successor of `K` per
  remaining ground argument — the per-level cost is the *definitional*
  identity `X ⊗ S K = X ⊗ K ⊕ X`), weakened to `K ⊗ ω` by `⊕ι-≤-⊗ω`;
* **`JAff-Sg-diag`** — the payoff: for *any* result type `τ`, from
  `JAff (ι ⇒ ι ⇒ τ) Tφ` and `JAff (ι ⇒ ι) Tγ` the ground diagonal
  `λ Ta → Tφ Ta (Tγ Ta)` is `JAff (ι ⇒ τ)` — substitute `Tγ`'s bound into
  the zone and absorb. This subsumes `AffBounded-Sg-diag` (`τ = ι`) and
  every rung `Affₙ` of the ladder in one statement.

The fundamental theorem over this class is `MultHereditaryFNT`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryFAffN
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left ; ⊕-assoc)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (_<_ ; ε₀ ; ⊗-mono-left ; ⊗-mono-right ; ⊕-mono-right ;
        ⊕-increasing-right ; ⊕-<-ε₀)
open import Claude.BrouwerOrdinals.Affine fe
 using (⊗-assoc ; ⊕-increasing-left)
open import Claude.BrouwerOrdinals.AffineClosure fe
 using (x-≤-x⊗ ; Z<ε₀ ; ι<ε₀)
open import Claude.BrouwerOrdinals.MultAffine fe using (ω-pos)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; ω-valid ; validMult-⊗)
open import Claude.DialogueTreeHeight.MultHereditaryF fe
 using (𝕋 ; GoodT ; Torbit ; GoodT-⊕)
open import Claude.DialogueTreeHeight.MultHereditaryFAff fe
 using (AffBounded ; AffBounded-orbit ; ⊕-dup-≤-⊗ω)
open import Claude.DialogueTreeHeight.MultHereditaryFAff2 fe
 using (S-≤-⊗ω)

\end{code}

Small arithmetic: `S` commutes with adding a numeral (numerals have no limit
stage, so this is a genuine equality), a numeral added to a positive `K` is
absorbed by `K ⊗ ω`, and a middle summand can be inserted into a sum.

\begin{code}

S-⊕-ι : (a : 𝓑) (m : ℕ) → (S a ⊕ ι[ m ]) ＝ S (a ⊕ ι[ m ])
S-⊕-ι a zero     = refl
S-⊕-ι a (succ m) = ap S (S-⊕-ι a m)

⊕ι-≤-⊗ι : (K : 𝓑) → S Z ≤ K → (m : ℕ) → (K ⊕ ι[ m ]) ≤ (K ⊗ ι[ succ m ])
⊕ι-≤-⊗ι K K+ zero     = ⊕-increasing-left Z K
⊕ι-≤-⊗ι K K+ (succ m) =
 ≤-trans (≤-S (⊕ι-≤-⊗ι K K+ m)) (⊕-mono-right (K ⊗ ι[ succ m ]) K+)

⊕ι-≤-⊗ω : (K : 𝓑) → S Z ≤ K → (m : ℕ) → (K ⊕ ι[ m ]) ≤ (K ⊗ ω)
⊕ι-≤-⊗ω K K+ m =
 ≤-trans (⊕ι-≤-⊗ι K K+ m) (⊗-mono-right K (≤-L-upper-bound ι[_] (succ m)))

⊕-insert-mid : (a b c : 𝓑) → (a ⊕ c) ≤ ((a ⊕ b) ⊕ c)
⊕-insert-mid a b c =
 transport (λ z → (a ⊕ c) ≤ z) ((⊕-assoc a b c) ⁻¹)
           (⊕-mono-right a (⊕-increasing-left b c))

\end{code}

The zone predicate, its collapse structure, and its depth.

\begin{code}

BoundT : (τ : type) → 𝕋 τ → (𝓑 → 𝓑) → 𝓑 → 𝓑 → 𝓤₀ ̇
BoundT ι                a D c M = (w : 𝓑) → a w ≤ ((D w ⊕ c) ⊗ M)
BoundT (ι ⇒ τ)          T D c M = (T₁ : 𝓑 → 𝓑)
                                → BoundT τ (T T₁) (λ w → D w ⊕ T₁ w) c M
BoundT ((σ₁ ⇒ σ₂) ⇒ τ)  T D c M = 𝟙

Collapses : type → 𝓤₀ ̇
Collapses ι                = 𝟘
Collapses (ι ⇒ τ)          = Collapses τ
Collapses ((σ₁ ⇒ σ₂) ⇒ τ)  = 𝟙

dp : type → ℕ
dp ι                = 0
dp (ι ⇒ τ)          = succ (dp τ)
dp ((σ₁ ⇒ σ₂) ⇒ τ)  = 0

JAff : (τ : type) → 𝕋 τ → 𝓤₀ ̇
JAff τ T = Σ D ꞉ (𝓑 → 𝓑) , Σ c ꞉ 𝓑 , Σ M ꞉ 𝓑 ,
              GoodT ι D × (c < ε₀) × ValidMult M × BoundT τ T D c M

\end{code}

Monotonicity in the summand and the multiplier, collapse, and the trivial
`JAff` data past a function argument.

\begin{code}

BoundT-mono-D : (τ : type) (T : 𝕋 τ) (D D′ : 𝓑 → 𝓑) (c M : 𝓑)
              → ((w : 𝓑) → D w ≤ D′ w)
              → BoundT τ T D c M → BoundT τ T D′ c M
BoundT-mono-D ι               a D D′ c M h b =
 λ w → ≤-trans (b w) (⊗-mono-left (⊕-mono-left (h w) c) M)
BoundT-mono-D (ι ⇒ τ)         T D D′ c M h b =
 λ T₁ → BoundT-mono-D τ (T T₁) (λ w → D w ⊕ T₁ w) (λ w → D′ w ⊕ T₁ w) c M
          (λ w → ⊕-mono-left (h w) (T₁ w)) (b T₁)
BoundT-mono-D ((σ₁ ⇒ σ₂) ⇒ τ) T D D′ c M h b = ⋆

BoundT-mono-M : (τ : type) (T : 𝕋 τ) (D : 𝓑 → 𝓑) (c M M′ : 𝓑)
              → M ≤ M′ → BoundT τ T D c M → BoundT τ T D c M′
BoundT-mono-M ι               a D c M M′ h b =
 λ w → ≤-trans (b w) (⊗-mono-right (D w ⊕ c) h)
BoundT-mono-M (ι ⇒ τ)         T D c M M′ h b =
 λ T₁ → BoundT-mono-M τ (T T₁) (λ w → D w ⊕ T₁ w) c M M′ h (b T₁)
BoundT-mono-M ((σ₁ ⇒ σ₂) ⇒ τ) T D c M M′ h b = ⋆

BoundT-collapse : (τ : type) → Collapses τ → (T : 𝕋 τ) (D : 𝓑 → 𝓑) (c M : 𝓑)
                → BoundT τ T D c M
BoundT-collapse (ι ⇒ τ)         cw T D c M =
 λ T₁ → BoundT-collapse τ cw (T T₁) (λ w → D w ⊕ T₁ w) c M
BoundT-collapse ((σ₁ ⇒ σ₂) ⇒ τ) cw T D c M = ⋆

JAff-collapse : (τ : type) → Collapses τ → (T : 𝕋 τ) → JAff τ T
JAff-collapse τ cw T =
 (λ _ → Z) , Z , ω
 , ((λ w _ → Z<ε₀) , (λ w w′ _ → ≤-Z))
 , Z<ε₀ , ω-valid , BoundT-collapse τ cw T (λ _ → Z) Z ω

\end{code}

The combinator shapes: identity, successor, constant, left-addition, the
outer `K` projection (for any second type), dead-argument insertion, and the
recursor's partial application — jointly in its start and count arguments.

\begin{code}

JAff-id : JAff (ι ⇒ ι) (λ T → T)
JAff-id = (λ _ → Z) , Z , ω
 , ((λ w _ → Z<ε₀) , (λ w w′ _ → ≤-Z)) , Z<ε₀ , ω-valid
 , (λ T w → ≤-trans (⊕-increasing-left Z (T w)) (x-≤-x⊗ (Z ⊕ T w) ω ω-pos))

JAff-S : JAff (ι ⇒ ι) (λ T w → S (T w))
JAff-S = (λ _ → Z) , ι[ 1 ] , ω
 , ((λ w _ → Z<ε₀) , (λ w w′ _ → ≤-Z)) , ι<ε₀ 1 , ω-valid
 , (λ T w → ≤-trans (≤-S (⊕-increasing-left Z (T w)))
                    (x-≤-x⊗ ((Z ⊕ T w) ⊕ ι[ 1 ]) ω ω-pos))

JAff-const : (Ta : 𝕋 ι) → GoodT ι Ta → JAff (ι ⇒ ι) (λ Tb → Ta)
JAff-const Ta gTa = Ta , Z , ω , gTa , Z<ε₀ , ω-valid
 , (λ Tb w → ≤-trans (⊕-increasing-right (Ta w) (Tb w))
                     (x-≤-x⊗ (Ta w ⊕ Tb w) ω ω-pos))

JAff-add : (C : 𝕋 ι) → GoodT ι C → JAff (ι ⇒ ι) (λ Tν w → C w ⊕ Tν w)
JAff-add C gC = C , Z , ω , gC , Z<ε₀ , ω-valid
 , (λ Tν w → x-≤-x⊗ (C w ⊕ Tν w) ω ω-pos)

JAff-K-outer : (τ : type) → JAff (ι ⇒ τ ⇒ ι) (λ Ta Tb → Ta)
JAff-K-outer ι =
 (λ _ → Z) , Z , ω
 , ((λ w _ → Z<ε₀) , (λ w w′ _ → ≤-Z)) , Z<ε₀ , ω-valid
 , (λ Ta Tb w → ≤-trans (⊕-increasing-left Z (Ta w))
                 (≤-trans (⊕-increasing-right (Z ⊕ Ta w) (Tb w))
                          (x-≤-x⊗ ((Z ⊕ Ta w) ⊕ Tb w) ω ω-pos)))
JAff-K-outer (τ₁ ⇒ τ₂) =
 (λ _ → Z) , Z , ω
 , ((λ w _ → Z<ε₀) , (λ w w′ _ → ≤-Z)) , Z<ε₀ , ω-valid
 , (λ Ta → ⋆)

JAff-insert : (σ : type) (Ta : 𝕋 σ) → JAff σ Ta → JAff (ι ⇒ σ) (λ Tb → Ta)
JAff-insert σ Ta (D , c , M , gD , c<ε₀ , vM , b) =
 D , c , M , gD , c<ε₀ , vM
 , (λ Tb → BoundT-mono-D σ Ta D (λ w → D w ⊕ Tb w) c M
             (λ w → ⊕-increasing-right (D w) (Tb w)) b)

JAff-to-AffBounded : (Tg : 𝕋 (ι ⇒ ι)) → JAff (ι ⇒ ι) Tg → AffBounded Tg
JAff-to-AffBounded Tg (D , c , M , gD , c<ε₀ , vM , b) =
 D , c , M , gD , c<ε₀ , vM
 , (λ T w → transport (λ z → Tg T w ≤ (z ⊗ M)) (⊕-assoc (D w) (T w) c) (b T w))

JAff-Iter : (Tg : 𝕋 (ι ⇒ ι)) → AffBounded Tg
          → JAff (ι ⇒ ι ⇒ ι) (λ Ta Tν w → Torbit Tg Ta w ⊕ Tν w)
JAff-Iter Tg affTg = step (AffBounded-orbit Tg affTg)
 where
  step : AffBounded (λ Ta → Torbit Tg Ta)
       → JAff (ι ⇒ ι ⇒ ι) (λ Ta Tν w → Torbit Tg Ta w ⊕ Tν w)
  step (D , c , M , gD , c<ε₀ , vM@(M+ , _ , _) , ob) =
   D , c , (M ⊗ ω) , gD , c<ε₀ , validMult-⊗ vM ω-valid , bound
   where
    bound : (Ta Tν : 𝓑 → 𝓑) (w : 𝓑)
          → (Torbit Tg Ta w ⊕ Tν w)
            ≤ ((((D w ⊕ Ta w) ⊕ Tν w) ⊕ c) ⊗ (M ⊗ ω))
    bound Ta Tν w =
     ≤-trans (⊕-mono-left orb≤ (Tν w))
      (≤-trans (⊕-mono-right (X ⊗ M) Tν≤)
               (⊗-mono-right X (S-≤-⊗ω M M+)))
     where
      X : 𝓑
      X = ((D w ⊕ Ta w) ⊕ Tν w) ⊕ c

      orb≤ : Torbit Tg Ta w ≤ (X ⊗ M)
      orb≤ = ≤-trans (ob Ta w)
              (⊗-mono-left
                (transport (λ z → z ≤ X) (⊕-assoc (D w) (Ta w) c)
                           (⊕-insert-mid (D w ⊕ Ta w) (Tν w) c)) M)

      Tν≤ : Tν w ≤ X
      Tν≤ = ≤-trans (⊕-increasing-left (D w ⊕ Ta w) (Tν w))
                    (⊕-increasing-right ((D w ⊕ Ta w) ⊕ Tν w) c)

\end{code}

The absorption engine. Re-basing the accumulated summand from `A` to `B`
costs one successor of `K` per remaining ground argument (the definitional
identity `X ⊗ S K = X ⊗ K ⊕ X` at each level), totalling `K ⊕ ι[depth + 1]`
in the multiplier.

\begin{code}

BoundT-absorb : (τ : type) (T : 𝕋 τ) (A B : 𝓑 → 𝓑) (c c′ M K : 𝓑)
              → ((w : 𝓑) → A w ≤ ((B w ⊕ c′) ⊗ K))
              → c ≤ c′
              → BoundT τ T A c M
              → BoundT τ T B c′ ((K ⊕ ι[ succ (dp τ) ]) ⊗ M)
BoundT-absorb ι a A B c c′ M K h q b = λ w →
 ≤-trans (b w)
  (transport (λ z → ((A w ⊕ c) ⊗ M) ≤ z) (⊗-assoc (B w ⊕ c′) (S K) M)
    (⊗-mono-left
      (≤-trans (⊕-mono-left (h w) c)
        (≤-trans (⊕-mono-right ((B w ⊕ c′) ⊗ K) q)
                 (⊕-mono-right ((B w ⊕ c′) ⊗ K)
                               (⊕-increasing-left (B w) c′))))
      M))
BoundT-absorb (ι ⇒ τ) T A B c c′ M K h q b = λ T₁ →
 transport
  (λ z → BoundT τ (T T₁) (λ w → B w ⊕ T₁ w) c′ (z ⊗ M))
  (S-⊕-ι K (succ (dp τ)))
  (BoundT-absorb τ (T T₁)
    (λ w → A w ⊕ T₁ w) (λ w → B w ⊕ T₁ w) c c′ M (S K)
    (λ w → ≤-trans (⊕-mono-left (h w) (T₁ w))
            (≤-trans (⊕-mono-left
                       (⊗-mono-left (⊕-insert-mid (B w) (T₁ w) c′) K)
                       (T₁ w))
              (⊕-mono-right (((B w ⊕ T₁ w) ⊕ c′) ⊗ K)
                (≤-trans (⊕-increasing-left (B w) (T₁ w))
                         (⊕-increasing-right (B w ⊕ T₁ w) c′)))))
    q (b T₁))
BoundT-absorb ((σ₁ ⇒ σ₂) ⇒ τ) T A B c c′ M K h q b = ⋆

\end{code}

The payoff: the uniform ground-`S` diagonal, for any result type `τ`.
Substituting `Tγ`'s bound into `Tφ`'s zone gives the accumulated summand
`(Dφ ⊕ Ta) ⊕ Tγ Ta`, which is dominated by the target zone
`((Dφ ⊕ Dγ) ⊕ Ta) ⊕ (cγ ⊕ cφ)` times `K = Mγ ⊗ ω` (the raw copy and the
`⊗ Mγ` copy of the zone merge by one duplication); `BoundT-absorb` re-bases,
and the multiplier weakens to `M★ = ((Mγ ⊗ ω) ⊗ ω) ⊗ Mφ` — a `ValidMult`,
independent of `τ`.

\begin{code}

JAff-Sg-diag : (τ : type) (Tφ : 𝕋 (ι ⇒ ι ⇒ τ)) (Tγ : 𝕋 (ι ⇒ ι))
             → JAff (ι ⇒ ι ⇒ τ) Tφ → JAff (ι ⇒ ι) Tγ
             → JAff (ι ⇒ τ) (λ Ta → Tφ Ta (Tγ Ta))
JAff-Sg-diag τ Tφ Tγ (Dφ , cφ , Mφ , gDφ , cφ<ε₀ , vMφ , bφ)
                     (Dγ , cγ , Mγ , gDγ , cγ<ε₀ , vMγ@(Mγ+ , _ , _) , bγ) =
 (λ w → Dφ w ⊕ Dγ w) , (cγ ⊕ cφ) , (((Mγ ⊗ ω) ⊗ ω) ⊗ Mφ)
 , GoodT-⊕ Dφ Dγ gDφ gDγ
 , ⊕-<-ε₀ cγ cφ cγ<ε₀ cφ<ε₀
 , validMult-⊗ (validMult-⊗ (validMult-⊗ vMγ ω-valid) ω-valid) vMφ
 , bound
 where
  K : 𝓑
  K = Mγ ⊗ ω

  K+ : S Z ≤ K
  K+ = ≤-trans Mγ+ (x-≤-x⊗ Mγ ω ω-pos)

  bound : (Ta : 𝓑 → 𝓑)
        → BoundT τ (Tφ Ta (Tγ Ta))
                 (λ w → (Dφ w ⊕ Dγ w) ⊕ Ta w) (cγ ⊕ cφ) (((Mγ ⊗ ω) ⊗ ω) ⊗ Mφ)
  bound Ta =
   BoundT-mono-M τ (Tφ Ta (Tγ Ta)) B (cγ ⊕ cφ)
     ((K ⊕ ι[ succ (dp τ) ]) ⊗ Mφ) (((Mγ ⊗ ω) ⊗ ω) ⊗ Mφ)
     (⊗-mono-left (⊕ι-≤-⊗ω K K+ (succ (dp τ))) Mφ)
     (BoundT-absorb τ (Tφ Ta (Tγ Ta)) A B cφ (cγ ⊕ cφ) Mφ K hyp
       (⊕-increasing-left cγ cφ) (bφ Ta (Tγ Ta)))
   where
    A B : 𝓑 → 𝓑
    A = λ w → (Dφ w ⊕ Ta w) ⊕ Tγ Ta w
    B = λ w → (Dφ w ⊕ Dγ w) ⊕ Ta w

    hyp : (w : 𝓑) → A w ≤ ((B w ⊕ (cγ ⊕ cφ)) ⊗ K)
    hyp w = ≤-trans step₁ (≤-trans step₂
             (transport (λ z → ((X ⊗ Mγ) ⊕ (X ⊗ Mγ)) ≤ z)
                        (⊗-assoc X Mγ ω)
                        (⊕-dup-≤-⊗ω (X ⊗ Mγ))))
     where
      X : 𝓑
      X = B w ⊕ (cγ ⊕ cφ)

      Dφ⊕Ta≤X : (Dφ w ⊕ Ta w) ≤ X
      Dφ⊕Ta≤X =
       ≤-trans (⊕-mono-left (⊕-increasing-right (Dφ w) (Dγ w)) (Ta w))
               (⊕-increasing-right (B w) (cγ ⊕ cφ))

      zone≤X : ((Dγ w ⊕ Ta w) ⊕ cγ) ≤ X
      zone≤X =
       ≤-trans (⊕-mono-left
                 (⊕-mono-left (⊕-increasing-left (Dφ w) (Dγ w)) (Ta w)) cγ)
               (⊕-mono-right (B w) (⊕-increasing-right cγ cφ))

      step₁ : A w ≤ (X ⊕ (X ⊗ Mγ))
      step₁ = ≤-trans (⊕-mono-left Dφ⊕Ta≤X (Tγ Ta w))
               (⊕-mono-right X
                 (≤-trans (bγ Ta w) (⊗-mono-left zone≤X Mγ)))

      step₂ : (X ⊕ (X ⊗ Mγ)) ≤ ((X ⊗ Mγ) ⊕ (X ⊗ Mγ))
      step₂ = ⊕-mono-left (x-≤-x⊗ X Mγ Mγ+) (X ⊗ Mγ)

\end{code}
