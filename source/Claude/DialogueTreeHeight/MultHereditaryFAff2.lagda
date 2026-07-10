The binary joint affine class `Aff₂`: inner-affine functionals of *two* ground
transformer arguments, jointly — the data the all-ground `S` diagonal needs.

`MultHereditaryFT`'s refinement carries `AffBounded` only at `ι ⇒ ι`, so its
fragment `T⁺` misses the all-ground instance `Sg★` (`ρ = σ = τ = ι`): the
diagonal `λ Ta → Tφ Ta (Tγ Ta)` must be inner-affine, but the curried data
"`Tφ Ta` is `AffBounded` for each `Ta`" varies with `Ta` and cannot be summed
into one bound. The fix is the classical joint-bound move (cf. `Hereditary`'s
`JointAff`, here at the transformer level): carry a *single* bound with both
arguments inside one multiplied zone,

  `Aff₂ T = Σ D c M , … × (∀ T₁ T₂ w → T T₁ T₂ w ≤ (D w ⊕ (T₁ w ⊕ (T₂ w ⊕ c))) ⊗ M)`.

Because the inner zone is quasi-commutative — any reordering or duplication of
summands costs at most one factor of `ω` in the multiplier (`⊕-dup/trip/quad`)
— the joint bound has all the closure properties the fragment needs:

* `Aff₂-apply`: fixing the first argument (a `GoodT` transformer) lands in
  `AffBounded` with summand `D ⊕ T₁` — currying is just `⊕`-associativity;
* `Aff₂-K` and `Aff₂-insert`: the two projections are jointly affine
  (`insert` needs the ignored argument slipped into the zone);
* `Aff₂-Iter`: the recursor's two ground arguments (start and count) are
  *jointly* affine — from `AffBounded-orbit`, paying `S M ≤ M ⊗ ω` to absorb
  the added count;
* `AffBounded-Sg-diag` — the payoff: from `Aff₂ Tφ` and `AffBounded Tγ`, the
  ground diagonal `λ Ta → Tφ Ta (Tγ Ta)` is `AffBounded`, by substituting
  `Tγ`'s bound into `Tφ`'s zone and absorbing the doubled zone with one `ω`.

This is the arithmetic for a fragment containing `MultHereditaryT`'s `T★`
(with `Sg★`) *inside* the Design-F predicate — assembled in
`MultHereditaryFJT`. Capping the joint data at two arguments is a real
restriction (an `S` producing an all-ground *binary* result would demand
`Aff₃`, and so on); the arities form a ladder whose general rung is the
`n`-ary zone calculus, not built here.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultHereditaryFAff2
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
 using (x-≤-x⊗ ; y-≤-⊗ ; Z<ε₀)
open import Claude.BrouwerOrdinals.MultAffine fe using (ω-pos)
open import Claude.BrouwerOrdinals.MultDominated fe
 using (ValidMult ; ω-valid ; validMult-⊗)
open import Claude.DialogueTreeHeight.MultHereditaryF fe
 using (𝕋 ; GoodT ; Torbit ; GoodT-⊕)
open import Claude.DialogueTreeHeight.MultHereditaryFAff fe
 using (AffBounded ; AffBounded-orbit)

\end{code}

Two more absorption facts in the `⊕-dup/trip` family: a quadruple sum is
below `⊗ ω`, and a successor is absorbed by a positive multiplier's `⊗ ω`
(used to add one summand outside an existing product).

\begin{code}

⊕-quad-≤-⊗ω : (x : 𝓑) → (x ⊕ (x ⊕ (x ⊕ x))) ≤ (x ⊗ ω)
⊕-quad-≤-⊗ω x =
 transport (λ z → z ≤ (x ⊗ ω))
           (⊕-assoc (x ⊕ x) x x ∙ ⊕-assoc x x (x ⊕ x))
           (≤-trans left-nested (⊗-mono-right x (≤-L-upper-bound ι[_] 4)))
 where
  left-nested : (((x ⊕ x) ⊕ x) ⊕ x) ≤ (x ⊗ ι[ 4 ])
  left-nested =
   ⊕-mono-left (⊕-mono-left (⊕-mono-left (⊕-increasing-left Z x) x) x) x

S-≤-⊗ω : (M : 𝓑) → S Z ≤ M → S M ≤ (M ⊗ ω)
S-≤-⊗ω M M+ =
 ≤-trans (⊕-mono-right M M+)
  (≤-trans (⊕-mono-left (⊕-increasing-left Z M) M)
           (⊗-mono-right M (≤-L-upper-bound ι[_] 2)))

\end{code}

The class.

\begin{code}

Aff₂ : 𝕋 (ι ⇒ ι ⇒ ι) → 𝓤₀ ̇
Aff₂ T =
 Σ D ꞉ (𝓑 → 𝓑) , Σ c ꞉ 𝓑 , Σ M ꞉ 𝓑 ,
    GoodT ι D × (c < ε₀) × ValidMult M
  × ((T₁ T₂ : 𝓑 → 𝓑) (w : 𝓑)
       → T T₁ T₂ w ≤ ((D w ⊕ (T₁ w ⊕ (T₂ w ⊕ c))) ⊗ M))

\end{code}

Currying: fixing the first argument gives an `AffBounded` section, the fixed
argument joining the summand (`⊕`-associativity, no arithmetic).

\begin{code}

Aff₂-apply : (T : 𝕋 (ι ⇒ ι ⇒ ι)) → Aff₂ T
           → (T₁ : 𝓑 → 𝓑) → GoodT ι T₁ → AffBounded (T T₁)
Aff₂-apply T (D , c , M , gD , c<ε₀ , vM , jb) T₁ gT₁ =
 (λ w → D w ⊕ T₁ w) , c , M , GoodT-⊕ D T₁ gD gT₁ , c<ε₀ , vM , bound
 where
  bound : (T₂ : 𝓑 → 𝓑) (w : 𝓑)
        → T T₁ T₂ w ≤ (((D w ⊕ T₁ w) ⊕ (T₂ w ⊕ c)) ⊗ M)
  bound T₂ w =
   transport (λ z → T T₁ T₂ w ≤ (z ⊗ M))
             ((⊕-assoc (D w) (T₁ w) (T₂ w ⊕ c)) ⁻¹)
             (jb T₁ T₂ w)

\end{code}

The projections.

\begin{code}

Aff₂-K : Aff₂ (λ T₁ T₂ → T₁)
Aff₂-K =
 (λ _ → Z) , Z , ω
 , ((λ w _ → Z<ε₀) , (λ w w′ _ → ≤-Z))
 , Z<ε₀ , ω-valid , bound
 where
  bound : (T₁ T₂ : 𝓑 → 𝓑) (w : 𝓑)
        → T₁ w ≤ ((Z ⊕ (T₁ w ⊕ (T₂ w ⊕ Z))) ⊗ ω)
  bound T₁ T₂ w =
   ≤-trans (⊕-increasing-right (T₁ w) (T₂ w))
    (≤-trans (⊕-increasing-left Z (T₁ w ⊕ T₂ w))
             (x-≤-x⊗ (Z ⊕ (T₁ w ⊕ T₂ w)) ω ω-pos))

Aff₂-insert : (Ta : 𝕋 (ι ⇒ ι)) → AffBounded Ta → Aff₂ (λ T₁ → Ta)
Aff₂-insert Ta (D , c , M , gD , c<ε₀ , vM , aff) =
 D , c , M , gD , c<ε₀ , vM , bound
 where
  bound : (T₁ T₂ : 𝓑 → 𝓑) (w : 𝓑)
        → Ta T₂ w ≤ ((D w ⊕ (T₁ w ⊕ (T₂ w ⊕ c))) ⊗ M)
  bound T₁ T₂ w =
   ≤-trans (aff T₂ w)
    (⊗-mono-left (⊕-mono-right (D w) (⊕-increasing-left (T₁ w) (T₂ w ⊕ c))) M)

\end{code}

The recursor's two ground arguments, jointly. From `AffBounded-orbit`, the
orbit is inner-affine in the start; adding the count `Tν w` costs one extra
summand, absorbed as `(Z′ ⊗ M) ⊕ Z′ = Z′ ⊗ (S M) ≤ Z′ ⊗ (M ⊗ ω)`.

\begin{code}

Aff₂-Iter : (Tg : 𝕋 (ι ⇒ ι)) → AffBounded Tg
          → Aff₂ (λ Ta Tν w → Torbit Tg Ta w ⊕ Tν w)
Aff₂-Iter Tg affTg = step (AffBounded-orbit Tg affTg)
 where
  step : AffBounded (λ Ta → Torbit Tg Ta)
       → Aff₂ (λ Ta Tν w → Torbit Tg Ta w ⊕ Tν w)
  step (D , c , M , gD , c<ε₀ , vM@(M+ , _ , _) , ob) =
   D , c , (M ⊗ ω) , gD , c<ε₀ , validMult-⊗ vM ω-valid , bound
   where
    bound : (Ta Tν : 𝓑 → 𝓑) (w : 𝓑)
          → (Torbit Tg Ta w ⊕ Tν w)
            ≤ ((D w ⊕ (Ta w ⊕ (Tν w ⊕ c))) ⊗ (M ⊗ ω))
    bound Ta Tν w =
     ≤-trans (⊕-mono-left orb≤ (Tν w))
      (≤-trans (⊕-mono-right (Z′ ⊗ M) Tν≤)
               (⊗-mono-right Z′ (S-≤-⊗ω M M+)))
     where
      Z′ : 𝓑
      Z′ = D w ⊕ (Ta w ⊕ (Tν w ⊕ c))

      orb≤ : Torbit Tg Ta w ≤ (Z′ ⊗ M)
      orb≤ = ≤-trans (ob Ta w)
              (⊗-mono-left
                (⊕-mono-right (D w)
                  (⊕-mono-right (Ta w) (⊕-increasing-left (Tν w) c))) M)

      Tν≤ : Tν w ≤ Z′
      Tν≤ = ≤-trans (⊕-increasing-right (Tν w) c)
             (≤-trans (⊕-increasing-left (Ta w) (Tν w ⊕ c))
                      (⊕-increasing-left (D w) (Ta w ⊕ (Tν w ⊕ c))))

\end{code}

The payoff: the all-ground `S` diagonal. Substituting `Tγ`'s bound into
`Tφ`'s zone leaves a `⊗ Mγ` term among the summands; enlarging the zone to
`base = (D_φ ⊕ D_γ) ⊕ (Ta ⊕ (c_γ ⊕ c_φ))` puts every summand below
`Y′ = base ⊗ (ω ⊗ M_γ)`, and the quadruple absorption packs the zone into
`Y′ ⊗ ω` — inner-affine at multiplier `((ω ⊗ M_γ) ⊗ ω) ⊗ M_φ`.

\begin{code}

AffBounded-Sg-diag : (Tφ : 𝕋 (ι ⇒ ι ⇒ ι)) (Tγ : 𝕋 (ι ⇒ ι))
                   → Aff₂ Tφ → AffBounded Tγ
                   → AffBounded (λ Ta → Tφ Ta (Tγ Ta))
AffBounded-Sg-diag Tφ Tγ (Dφ , cφ , Mφ , gDφ , cφ<ε₀ , vMφ , jφ)
                         (Dγ , cγ , Mγ , gDγ , cγ<ε₀ , vMγ , aγ) =
 (λ w → Dφ w ⊕ Dγ w) , (cγ ⊕ cφ) , (((ω ⊗ Mγ) ⊗ ω) ⊗ Mφ)
 , GoodT-⊕ Dφ Dγ gDφ gDγ
 , ⊕-<-ε₀ cγ cφ cγ<ε₀ cφ<ε₀
 , validMult-⊗ (validMult-⊗ (validMult-⊗ ω-valid vMγ) ω-valid) vMφ
 , bound
 where
  bound : (Ta : 𝓑 → 𝓑) (w : 𝓑)
        → Tφ Ta (Tγ Ta) w
          ≤ (((Dφ w ⊕ Dγ w) ⊕ (Ta w ⊕ (cγ ⊕ cφ))) ⊗ (((ω ⊗ Mγ) ⊗ ω) ⊗ Mφ))
  bound Ta w =
   transport (λ z → Tφ Ta (Tγ Ta) w ≤ z) (⊗-assoc base ((ω ⊗ Mγ) ⊗ ω) Mφ)
    (transport (λ z → Tφ Ta (Tγ Ta) w ≤ (z ⊗ Mφ)) (⊗-assoc base (ω ⊗ Mγ) ω)
      chain)
   where
    base : 𝓑
    base = (Dφ w ⊕ Dγ w) ⊕ (Ta w ⊕ (cγ ⊕ cφ))

    Y′ : 𝓑
    Y′ = base ⊗ (ω ⊗ Mγ)

    ωMγ+ : S Z ≤ (ω ⊗ Mγ)
    ωMγ+ = pr₁ (validMult-⊗ ω-valid vMγ)

    base≤Y′ : base ≤ Y′
    base≤Y′ = x-≤-x⊗ base (ω ⊗ Mγ) ωMγ+

    Dφ≤Y′ : Dφ w ≤ Y′
    Dφ≤Y′ = ≤-trans (⊕-increasing-right (Dφ w) (Dγ w))
             (≤-trans (⊕-increasing-right (Dφ w ⊕ Dγ w) (Ta w ⊕ (cγ ⊕ cφ)))
                      base≤Y′)

    Ta≤Y′ : Ta w ≤ Y′
    Ta≤Y′ = ≤-trans (⊕-increasing-right (Ta w) (cγ ⊕ cφ))
             (≤-trans (⊕-increasing-left (Dφ w ⊕ Dγ w) (Ta w ⊕ (cγ ⊕ cφ)))
                      base≤Y′)

    cφ≤Y′ : cφ ≤ Y′
    cφ≤Y′ = ≤-trans (⊕-increasing-left cγ cφ)
             (≤-trans (⊕-increasing-left (Ta w) (cγ ⊕ cφ))
              (≤-trans (⊕-increasing-left (Dφ w ⊕ Dγ w) (Ta w ⊕ (cγ ⊕ cφ)))
                       base≤Y′))

    zone-mono : (Dγ w ⊕ (Ta w ⊕ cγ)) ≤ base
    zone-mono =
     ≤-trans (⊕-mono-left (⊕-increasing-left (Dφ w) (Dγ w)) (Ta w ⊕ cγ))
             (⊕-mono-right (Dφ w ⊕ Dγ w)
                           (⊕-mono-right (Ta w) (⊕-increasing-right cγ cφ)))

    X≤Y′ : Tγ Ta w ≤ Y′
    X≤Y′ = ≤-trans (aγ Ta w)
            (≤-trans (⊗-mono-left zone-mono Mγ)
                     (⊗-mono-right base (y-≤-⊗ ω Mγ ω-pos)))

    packed : (Dφ w ⊕ (Ta w ⊕ (Tγ Ta w ⊕ cφ))) ≤ (Y′ ⊕ (Y′ ⊕ (Y′ ⊕ Y′)))
    packed =
     ≤-trans (⊕-mono-left Dφ≤Y′ (Ta w ⊕ (Tγ Ta w ⊕ cφ)))
      (⊕-mono-right Y′
        (≤-trans (⊕-mono-left Ta≤Y′ (Tγ Ta w ⊕ cφ))
          (⊕-mono-right Y′
            (≤-trans (⊕-mono-left X≤Y′ cφ)
                     (⊕-mono-right Y′ cφ≤Y′)))))

    chain : Tφ Ta (Tγ Ta) w ≤ ((Y′ ⊗ ω) ⊗ Mφ)
    chain = ≤-trans (jφ Ta (Tγ Ta) w)
             (⊗-mono-left (≤-trans packed (⊕-quad-≤-⊗ω Y′)) Mφ)

\end{code}
