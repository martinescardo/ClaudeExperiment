Affine composition via ω-polynomials (constructive) — the unblocked closure.

The affine class `f b ≤ (b ⊕ d) ⊗ ω^k` did *not* compose, because that needs
the fold lemma `(x ⊗ ω^k) ⊕ d ≤ (x ⊕ d) ⊗ ω^k`, false for `ω` (`ω²+1 > ω²`).
The fix is to carry the bound as a *polynomial*: a function `f : 𝓑 → 𝓑` is
poly-affine `PAff k d` when, for every polynomial bound `pb` on the input,

  `f b ≤ ⟦ (shift k pb) ⊞ d ⟧`        (input scaled by `ω^k`, plus constant `d`)

with `⊞` the *commutative* natural sum and `shift k` the right-distributing
scalar `ω^k`. Now composition closes by ordinary polynomial algebra
(`shift-⊞`, `shift-shift`, `⊞`-associativity): `PAff k d ∘ PAff k′ e` is
`PAff (k+k′) (shift k e ⊞ d)`. This is exactly the `K`/`S` building block that
the non-commutative `⊕`/`⊗` could not provide.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.PolyAffine
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import Ordinals.BrouwerCodes renaming (B to 𝓑)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.Dialogue using (B ; generic)
open import Claude.DialogueTreeHeight.Constructive fe
open import Claude.DialogueTreeHeight.Orbit fe
 using (ι[_] ; ω ; _⊗_ ; ⊕-mono-left ; ⊕-assoc)
open import Claude.BrouwerOrdinals.Epsilon0 fe
 using (⊕-mono-right ; _<_ ; ε₀ ; S-increasing ; ω^_ ; ω^-mono ;
        maxℕ ; _≤ℕ_ ; ≤ℕ-refl ; ≤ℕ-maxL ; ≤ℕ-maxR)
open import Claude.BrouwerOrdinals.Affine fe using (⊕-increasing-left)
open import Claude.BrouwerOrdinals.OmegaPoly fe

\end{code}

Associativity of `+ℕ` and of the natural sum `⊞`, and that `[]` is its right
unit — the algebra the composition needs.

\begin{code}

+ℕ-assoc : (a b c : ℕ) → ((a +ℕ b) +ℕ c) ＝ (a +ℕ (b +ℕ c))
+ℕ-assoc a b zero     = refl
+ℕ-assoc a b (succ c) = ap succ (+ℕ-assoc a b c)

⊞-[] : (p : Poly) → (p ⊞ []) ＝ p
⊞-[] []       = refl
⊞-[] (c ∷ cs) = refl

⊞-assoc : (p q r : Poly) → ((p ⊞ q) ⊞ r) ＝ (p ⊞ (q ⊞ r))
⊞-assoc []        q         r         = refl
⊞-assoc (c ∷ cs)  []        r         = refl
⊞-assoc (c ∷ cs)  (d ∷ ds)  []        = refl
⊞-assoc (c ∷ cs)  (d ∷ ds)  (e ∷ es)  =
 ap (_∷ ((cs ⊞ ds) ⊞ es)) (+ℕ-assoc c d e)
 ∙ ap ((c +ℕ (d +ℕ e)) ∷_) (⊞-assoc cs ds es)

\end{code}

The poly-affine class.

\begin{code}

PAff : (𝓑 → 𝓑) → 𝓤₀ ̇
PAff f = Σ k ꞉ ℕ , Σ d ꞉ Poly ,
           ((b : 𝓑) (pb : Poly) → b ≤ ⟦ pb ⟧ → f b ≤ ⟦ (shift k pb) ⊞ d ⟧)

\end{code}

Identity is poly-affine (`k = 0`, `d = []`).

\begin{code}

PAff-id : PAff (λ b → b)
PAff-id = 0 , [] ,
          (λ b pb b≤ → transport (λ z → b ≤ ⟦ z ⟧) ((⊞-[] pb) ⁻¹) b≤)

\end{code}

The successor / oracle increment `λ b → S b` is poly-affine (`k = 0`,
`d = [ 1 ]`): `S b ≤ S ⟦ pb ⟧ ≤ ⟦ pb ⟧ ⊕ ⟦ [ 1 ] ⟧ ≤ ⟦ pb ⊞ [ 1 ] ⟧`, the
last step by `poly-key`. Note `shift 0 pb = pb` definitionally.

\begin{code}

SZ≤⟦1⟧ : (S Z) ≤ ⟦ 1 ∷ [] ⟧
SZ≤⟦1⟧ = ⊕-increasing-left (ω ⊗ Z) ι[ 1 ]

S⟦⟧≤ : (pb : Poly) → S ⟦ pb ⟧ ≤ (⟦ pb ⟧ ⊕ ⟦ 1 ∷ [] ⟧)
S⟦⟧≤ pb = ⊕-mono-right ⟦ pb ⟧ SZ≤⟦1⟧

PAff-S : PAff (λ b → S b)
PAff-S = 0 , (1 ∷ []) ,
         (λ b pb b≤ →
           ≤-trans (≤-trans (≤-S b≤) (S⟦⟧≤ pb)) (poly-key pb (1 ∷ [])))

\end{code}

Constant transforms are poly-affine (`k = 0`, `d = c`): `⟦ c ⟧ ≤ ⟦ pb ⟧ ⊕
⟦ c ⟧ ≤ ⟦ pb ⊞ c ⟧`. This is the `K`-projection leaf.

\begin{code}

PAff-const : (c : Poly) → PAff (λ _ → ⟦ c ⟧)
PAff-const c = 0 , c ,
               (λ b pb b≤ → ≤-trans (⊕-increasing-left ⟦ pb ⟧ ⟦ c ⟧)
                                    (poly-key pb c))

\end{code}

The *additive* transform `λ a → a ⊕ ⟦c⟧` is poly-affine (`k = 0`, `d = c`):
`a ⊕ ⟦c⟧ ≤ ⟦pb⟧ ⊕ ⟦c⟧ ≤ ⟦pb ⊞ c⟧`. This is the height-transform shape of the
`Succ`/`Ω`-style combinators (increment by a constant).

\begin{code}

PAff-add : (c : Poly) → PAff (λ a → a ⊕ ⟦ c ⟧)
PAff-add c = 0 , c ,
             (λ b pb b≤ → ≤-trans (⊕-mono-left b≤ ⟦ c ⟧) (poly-key pb c))

\end{code}

The key result: poly-affine functions compose — the closure that was blocked.

\begin{code}

PAff-∘ : {f g : 𝓑 → 𝓑} → PAff f → PAff g → PAff (λ b → f (g b))
PAff-∘ {f} {g} (k , d , hf) (k′ , e , hg) =
 (k +ℕ k′) , ((shift k e) ⊞ d) , h
 where
  h : (b : 𝓑) (pb : Poly) → b ≤ ⟦ pb ⟧
    → f (g b) ≤ ⟦ (shift (k +ℕ k′) pb) ⊞ ((shift k e) ⊞ d) ⟧
  h b pb b≤ =
   transport (λ z → f (g b) ≤ ⟦ z ⟧) eq
             (hf (g b) ((shift k′ pb) ⊞ e) (hg b pb b≤))
   where
    eq : (shift k ((shift k′ pb) ⊞ e) ⊞ d)
       ＝ ((shift (k +ℕ k′) pb) ⊞ ((shift k e) ⊞ d))
    eq = ap (_⊞ d)
            (shift-⊞ k (shift k′ pb) e
             ∙ ap (_⊞ shift k e) (shift-shift k k′ pb))
       ∙ ⊞-assoc (shift (k +ℕ k′) pb) (shift k e) d

\end{code}

The payoff: a poly-affine function maps a polynomially-bounded input to an
output `< ε₀` (the bound is a polynomial, and every polynomial is `< ε₀`).

\begin{code}

PAff-<-ε₀ : {f : 𝓑 → 𝓑} → PAff f
          → (b : 𝓑) (pb : Poly) → b ≤ ⟦ pb ⟧ → f b < ε₀
PAff-<-ε₀ (k , d , hf) b pb b≤ =
 ≤-trans (≤-S (hf b pb b≤)) (poly-<-ε₀ ((shift k pb) ⊞ d))

\end{code}

The bridge to the orbit lemma: the *orbit* `j ↦ fʲ b` of a poly-affine map,
from a polynomially-bounded start, is `< ε₀`. Each iterate stays
polynomially bounded (the poly bound iterates by `q ↦ shift k q ⊞ d`), so the
supremum is a supremum of ω-polynomials, `< ε₀` by `poly-family-<-ε₀`. This is
precisely the (first-order) orbit lemma to which the conjecture reduces — now
discharged for every poly-affine height transform, with `PAff-∘` supplying the
closure under the combinators.

\begin{code}

PAff-orbit : {f : 𝓑 → 𝓑} → PAff f
           → (b : 𝓑) (pb : Poly) → b ≤ ⟦ pb ⟧
           → L (λ j → iter f b j) < ε₀
PAff-orbit {f} (k , d , hf) b pb b≤ =
 ≤-trans (≤-S (≤-L-mono orbit-bound)) (poly-family-<-ε₀ Q)
 where
  Q : ℕ → Poly
  Q = iter (λ q → (shift k q) ⊞ d) pb
  orbit-bound : (j : ℕ) → iter f b j ≤ ⟦ Q j ⟧
  orbit-bound zero     = b≤
  orbit-bound (succ j) = hf (iter f b j) (Q j) (orbit-bound j)

\end{code}

Down to the *real* dialogue height. If a tree transform `f : B ℕ → B ℕ` has
its height controlled by a poly-affine map `f̂` — `height (f y) ≤ f̂ (height y)`,
the machine-checked form of "depth cannot see itself" for `f` — then the
orbit of *heights* `k ↦ height (fᵏ x)` is `< ε₀`. This is the conjecture's
orbit lemma, reduced *exactly* to the poly-affineness of the height transform
(no monotonicity needed: `PAff` bounds `f̂ b` for every `b` below a polynomial,
so each iterate's poly bound feeds the next).

\begin{code}

transform-orbit
 : (f : B ℕ → B ℕ) (f̂ : 𝓑 → 𝓑) → PAff f̂
 → ((y : B ℕ) → height (f y) ≤ f̂ (height y))
 → (x : B ℕ) (px : Poly) → height x ≤ ⟦ px ⟧
 → L (λ k → height (iter f x k)) < ε₀
transform-orbit f f̂ (k , d , hf) htrans x px hx≤ =
 ≤-trans (≤-S (≤-L-mono orbit-bnd)) (poly-family-<-ε₀ Q)
 where
  Q : ℕ → Poly
  Q = iter (λ q → (shift k q) ⊞ d) px
  orbit-bnd : (j : ℕ) → height (iter f x j) ≤ ⟦ Q j ⟧
  orbit-bnd zero     = hx≤
  orbit-bnd (succ j) =
   ≤-trans (htrans (iter f x j)) (hf (height (iter f x j)) (Q j) (orbit-bnd j))

\end{code}

An unconditional instance: iterating the oracle `generic` (each application
raises the height by one, `height (generic y) ≤ S (height y) = (λ a → S a)
(height y)`, and `λ a → S a` is poly-affine `PAff-S`). So the orbit of heights
of the oracle iteration is `< ε₀`, with no hypotheses beyond a polynomial
bound on the start.

\begin{code}

generic-orbit : (x : B ℕ) (px : Poly) → height x ≤ ⟦ px ⟧
              → L (λ k → height (iter generic x k)) < ε₀
generic-orbit = transform-orbit generic (λ a → S a) PAff-S height-generic

\end{code}

More generally, any tree transform with a *constant additive* height increment
(`height (f y) ≤ height y ⊕ ⟦c⟧`) has orbit `< ε₀` — and such transforms are
closed under composition, the increments adding by the *commutative* natural
sum (`height (f (g y)) ≤ height y ⊕ ⟦cg ⊞ cf⟧`). So *every finite composite*
of oracle/relabelling operations has orbit of heights `< ε₀`, unconditionally.
(The remaining first-order case is the *nested recursor*, whose increment is
itself an orbit rather than a constant — the genuine tower step.)

\begin{code}

Additive : (B ℕ → B ℕ) → Poly → 𝓤₀ ̇
Additive f c = (y : B ℕ) → height (f y) ≤ (height y ⊕ ⟦ c ⟧)

add-∘ : {f g : B ℕ → B ℕ} {cf cg : Poly}
      → Additive f cf → Additive g cg → Additive (λ y → f (g y)) (cg ⊞ cf)
add-∘ {f} {g} {cf} {cg} af ag y =
 ≤-trans (af (g y))
   (≤-trans (⊕-mono-left (ag y) ⟦ cf ⟧)
     (transport (λ z → z ≤ (height y ⊕ ⟦ cg ⊞ cf ⟧))
                ((⊕-assoc (height y) ⟦ cg ⟧ ⟦ cf ⟧) ⁻¹)
                (⊕-mono-right (height y) (poly-key cg cf))))

add-orbit : (f : B ℕ → B ℕ) (c : Poly) → Additive f c
          → (x : B ℕ) (px : Poly) → height x ≤ ⟦ px ⟧
          → L (λ k → height (iter f x k)) < ε₀
add-orbit f c af = transform-orbit f (λ a → a ⊕ ⟦ c ⟧) (PAff-add c) af

\end{code}

Crucially, that orbit stays *polynomially bounded*: an additive step keeps the
polynomial *degree* fixed (only coefficients grow), so the whole orbit sits
below `ω^ι[L]` with `L = max (deg start, deg increment)`. This is what lets a
*nested* recursor feed its orbit — again a polynomial bound — to the next
level: the mechanism of the first-order tower `ω, ω², …, < ω^ω`.

\begin{code}

maxℕ-lub : (a b k : ℕ) → a ≤ℕ k → b ≤ℕ k → maxℕ a b ≤ℕ k
maxℕ-lub zero     b        k        _  hb = hb
maxℕ-lub (succ a) zero     k        ha _  = ha
maxℕ-lub (succ a) (succ b) (succ k) ha hb = maxℕ-lub a b k ha hb

ι-mono-ℕ : (n m : ℕ) → n ≤ℕ m → ι[ n ] ≤ ι[ m ]
ι-mono-ℕ zero     m        _ = ≤-Z
ι-mono-ℕ (succ n) (succ m) p = ≤-S (ι-mono-ℕ n m p)

length-⊞ : (p q : Poly) → length (p ⊞ q) ＝ maxℕ (length p) (length q)
length-⊞ []       q        = refl
length-⊞ (c ∷ cs) []       = refl
length-⊞ (c ∷ cs) (d ∷ ds) = ap succ (length-⊞ cs ds)

length-orbit : (c px : Poly) (j : ℕ)
             → length (iter (λ q → q ⊞ c) px j) ≤ℕ maxℕ (length px) (length c)
length-orbit c px zero     = ≤ℕ-maxL (length px) (length c)
length-orbit c px (succ j) =
 transport (_≤ℕ maxℕ (length px) (length c))
           ((length-⊞ (iter (λ q → q ⊞ c) px j) c) ⁻¹)
           (maxℕ-lub (length (iter (λ q → q ⊞ c) px j)) (length c)
                     (maxℕ (length px) (length c))
                     (length-orbit c px j) (≤ℕ-maxR (length px) (length c)))

add-orbit-poly : (f : B ℕ → B ℕ) (c : Poly) → Additive f c
               → (x : B ℕ) (px : Poly) → height x ≤ ⟦ px ⟧
               → L (λ k → height (iter f x k)) ≤ ω^ ι[ maxℕ (length px) (length c) ]
add-orbit-poly f c af x px hx≤ = ≤-L bound
 where
  Q : ℕ → Poly
  Q = iter (λ q → q ⊞ c)  px
  orbit-bnd : (k : ℕ) → height (iter f x k) ≤ ⟦ Q k ⟧
  orbit-bnd zero     = hx≤
  orbit-bnd (succ k) =
   ≤-trans (af (iter f x k))
     (≤-trans (⊕-mono-left (orbit-bnd k) ⟦ c ⟧) (poly-key (Q k) c))
  bound : (k : ℕ)
        → height (iter f x k) ≤ ω^ ι[ maxℕ (length px) (length c) ]
  bound k =
   ≤-trans (orbit-bnd k)
     (≤-trans (≤-trans (S-increasing ⟦ Q k ⟧) (poly-str (Q k)))
              (ω^-mono (ι-mono-ℕ (length (Q k)) (maxℕ (length px) (length c))
                                 (length-orbit c px k))))

\end{code}

The same poly-bounded orbit, at the level of an abstract *majorant* map
`g : 𝓑 → 𝓑` that is poly-additive (`b ≤ ⟦pb⟧ → g b ≤ ⟦pb ⊞ dg⟧`). This is
exactly the shape a hereditary recursor case needs: the iterated majorant's
orbit `sup_k gᵏ a` is a *polynomial* bound (`ω^ι[L]`), ready to feed the next
level as a constant.

\begin{code}

poly-map-orbit : (g : 𝓑 → 𝓑) (dg : Poly)
               → ((b : 𝓑) (pb : Poly) → b ≤ ⟦ pb ⟧ → g b ≤ ⟦ pb ⊞ dg ⟧)
               → (a : 𝓑) (pa : Poly) → a ≤ ⟦ pa ⟧
               → L (λ k → iter g a k) ≤ ω^ ι[ maxℕ (length pa) (length dg) ]
poly-map-orbit g dg hg a pa ha≤ = ≤-L bound
 where
  Q : ℕ → Poly
  Q = iter (λ q → q ⊞ dg) pa
  orbit-bnd : (k : ℕ) → iter g a k ≤ ⟦ Q k ⟧
  orbit-bnd zero     = ha≤
  orbit-bnd (succ k) = hg (iter g a k) (Q k) (orbit-bnd k)
  bound : (k : ℕ) → iter g a k ≤ ω^ ι[ maxℕ (length pa) (length dg) ]
  bound k =
   ≤-trans (orbit-bnd k)
     (≤-trans (≤-trans (S-increasing ⟦ Q k ⟧) (poly-str (Q k)))
              (ω^-mono (ι-mono-ℕ (length (Q k)) (maxℕ (length pa) (length dg))
                                 (length-orbit dg pa k))))

\end{code}

Completing the orbit toolkit: an iterated majorant may *multiply* its argument
(multiplicity `k`, when built via `S`), not merely add. But `nmul k` (k copies
summed) scales *coefficients*, never the *degree*, so the orbit is still
poly-bounded by the *same* `ω^ι[L]`. Hence the recursor orbit is polynomial for
*every* first-order iterated majorant, additive or multiplicative.

\begin{code}

≤ℕ-trans : (a b c : ℕ) → a ≤ℕ b → b ≤ℕ c → a ≤ℕ c
≤ℕ-trans zero     b        c        _ _ = ⋆
≤ℕ-trans (succ a) (succ b) (succ c) p q = ≤ℕ-trans a b c p q

nmul : ℕ → Poly → Poly
nmul zero     p = []
nmul (succ k) p = p ⊞ nmul k p

length-nmul-≤ : (k : ℕ) (q : Poly) → length (nmul k q) ≤ℕ length q
length-nmul-≤ zero     q = ⋆
length-nmul-≤ (succ k) q =
 transport (_≤ℕ length q) ((length-⊞ q (nmul k q)) ⁻¹)
   (maxℕ-lub (length q) (length (nmul k q)) (length q)
             (≤ℕ-refl (length q)) (length-nmul-≤ k q))

length-orbit-mult : (k : ℕ) (dg pa : Poly) (j : ℕ)
   → length (iter (λ q → nmul k q ⊞ dg) pa j) ≤ℕ maxℕ (length pa) (length dg)
length-orbit-mult k dg pa zero     = ≤ℕ-maxL (length pa) (length dg)
length-orbit-mult k dg pa (succ j) =
 transport (_≤ℕ maxℕ (length pa) (length dg))
           ((length-⊞ (nmul k Qj) dg) ⁻¹)
           (maxℕ-lub (length (nmul k Qj)) (length dg) (maxℕ (length pa) (length dg))
             (≤ℕ-trans (length (nmul k Qj)) (length Qj) (maxℕ (length pa) (length dg))
                       (length-nmul-≤ k Qj) (length-orbit-mult k dg pa j))
             (≤ℕ-maxR (length pa) (length dg)))
 where
  Qj : Poly
  Qj = iter (λ q → nmul k q ⊞ dg) pa j

poly-map-orbit-mult : (g : 𝓑 → 𝓑) (k : ℕ) (dg : Poly)
   → ((b : 𝓑) (pb : Poly) → b ≤ ⟦ pb ⟧ → g b ≤ ⟦ nmul k pb ⊞ dg ⟧)
   → (a : 𝓑) (pa : Poly) → a ≤ ⟦ pa ⟧
   → L (λ j → iter g a j) ≤ ω^ ι[ maxℕ (length pa) (length dg) ]
poly-map-orbit-mult g k dg hg a pa ha≤ = ≤-L bound
 where
  Q : ℕ → Poly
  Q = iter (λ q → nmul k q ⊞ dg) pa
  orbit-bnd : (j : ℕ) → iter g a j ≤ ⟦ Q j ⟧
  orbit-bnd zero     = ha≤
  orbit-bnd (succ j) = hg (iter g a j) (Q j) (orbit-bnd j)
  bound : (j : ℕ) → iter g a j ≤ ω^ ι[ maxℕ (length pa) (length dg) ]
  bound j =
   ≤-trans (orbit-bnd j)
     (≤-trans (≤-trans (S-increasing ⟦ Q j ⟧) (poly-str (Q j)))
              (ω^-mono (ι-mono-ℕ (length (Q j)) (maxℕ (length pa) (length dg))
                                 (length-orbit-mult k dg pa j))))

\end{code}
