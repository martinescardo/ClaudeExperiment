The `MultApplicative` fragment embeds into genuine first-order System T.

`MultApplicative` proved `height < ε₀` for a bespoke two-sort syntax
(`Gnd`/`Fun`) with its own interpretation `⟦_⟧G`/`⟦_⟧F` into the dialogue model.
For that theorem to be a statement about *System T*, and not an ad-hoc language,
the syntax must denote actual System T terms. This module verifies exactly that:
a translation into `Majorant`'s first-order combinatory syntax `T₁` (the genuine
`Ω/Zero/Succ/Iter/K/S/·`), with a proof that the dialogue interpretations agree
(`⟦ ⌜ x ⌝ ⟧₁ ＝ ⟦ x ⟧`).

The translation is forced and the agreement is *definitional* at every node —
`zero' = η 0`, `succ' = B-functor succ`, `iter' f x = kleisli-extension
(iter f x)`, `Ķ x y = x`, `Ş f g x = f x (g x)` all hold by computation — so the
proof is just `refl` glued by `ap`/`happly`/funext through the applications. Two
translations are worth naming:

* composition `compF f g` becomes `S (K f) g` (the standard combinator
  definition of `∘`), and
* the recursor `S`-diagonal `iterDiagF φ G` becomes **`S (Iter φ) G`** — an
  honest use of the `S` combinator with `Iter φ` as the shared-argument
  function. So the tower-driving term `MultApplicative` adds really is a System T
  term, and `MultApplicative`'s theorem is genuinely about System T dialogue
  trees: `height ⟦ ⌜ x ⌝G ⟧₁ < ε₀`.

This does not enlarge what is proved; it certifies the *scope* of
`MultApplicative` — its fragment is a bona fide sub-language of `T₁`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Claude.DialogueTreeHeight.MultApplicativeT
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import UF.Base using (ap₂ ; happly)
open import EffectfulForcing.MFPSAndVariations.Combinators using (iter)
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.CombinatoryT using (type ; ι ; _⇒_)
open import Claude.DialogueTreeHeight.Constructive fe using (height)
open import Claude.BrouwerOrdinals.Epsilon0 fe using (_<_ ; ε₀)
open import Claude.DialogueTreeHeight.Majorant fe
 using (T₁ ; Ω₁ ; Zero₁ ; Succ₁ ; Iter₁ ; K₁ ; S₁ ; _·₁_ ; ⟦_⟧₁)
open import Claude.DialogueTreeHeight.MultApplicative fe
 using (Gnd ; zeroG ; appG ;
        Fun ; ΩF ; succF ; iterF ; compF ; constF ; iterDiagF ;
        ⟦_⟧G ; ⟦_⟧F ; height-<-ε₀)

\end{code}

The translation. Ground terms go to `T₁ ι`, functions to `T₁ (ι ⇒ ι)`.
Composition uses `S (K f) g`; the recursor `S`-diagonal uses `S (Iter φ) G`.

\begin{code}

⌜_⌝G : Gnd → T₁ ι
⌜_⌝F : Fun → T₁ (ι ⇒ ι)

⌜ zeroG ⌝G    = Zero₁
⌜ appG f x ⌝G = ⌜ f ⌝F ·₁ ⌜ x ⌝G

⌜ ΩF ⌝F            = Ω₁
⌜ succF ⌝F         = Succ₁
⌜ iterF f x ⌝F     = Iter₁ ·₁ ⌜ f ⌝F ·₁ ⌜ x ⌝G
⌜ compF f g ⌝F     = S₁ ·₁ (K₁ ·₁ ⌜ f ⌝F) ·₁ ⌜ g ⌝F
⌜ constF x ⌝F      = K₁ ·₁ ⌜ x ⌝G
⌜ iterDiagF φ G ⌝F = S₁ ·₁ (Iter₁ ·₁ ⌜ φ ⌝F) ·₁ ⌜ G ⌝F

\end{code}

Agreement of the interpretations. Functions are compared as functions (needing
funext only where a translation is a genuine `λ` — composition, constant,
diagonal); the recursor cases compare `kleisli-extension (iter · ·)` by `ap₂` on
the two arguments. Every base case is `refl`.

\begin{code}

agreeG : (x : Gnd) → ⟦ ⌜ x ⌝G ⟧₁ ＝ ⟦ x ⟧G
agreeF : (f : Fun) → ⟦ ⌜ f ⌝F ⟧₁ ＝ ⟦ f ⟧F

agreeG zeroG      = refl
agreeG (appG f x) =
 happly (agreeF f) ⟦ ⌜ x ⌝G ⟧₁ ∙ ap ⟦ f ⟧F (agreeG x)

agreeF ΩF          = refl
agreeF succF       = refl
agreeF (iterF f x) =
 ap₂ (λ g y → kleisli-extension (iter g y)) (agreeF f) (agreeG x)
agreeF (compF f g) =
 dfunext fe (λ d → happly (agreeF f) (⟦ ⌜ g ⌝F ⟧₁ d)
                 ∙ ap ⟦ f ⟧F (happly (agreeF g) d))
agreeF (constF x)  = dfunext fe (λ _ → agreeG x)
agreeF (iterDiagF φ G) =
 dfunext fe (λ d → ap₂ (λ p q → kleisli-extension (iter p d) q)
                       (agreeF φ) (happly (agreeF G) d))

\end{code}

Hence every `MultApplicative` ground term is (the denotation of) a genuine
first-order System T term, and `MultApplicative`'s unconditional bound is a
statement about System T dialogue trees.

\begin{code}

embeds : (x : Gnd) → ⟦ ⌜ x ⌝G ⟧₁ ＝ ⟦ x ⟧G
embeds = agreeG

height-systemT-<-ε₀ : (x : Gnd) → height ⟦ ⌜ x ⌝G ⟧₁ < ε₀
height-systemT-<-ε₀ x =
 transport (λ z → height z < ε₀) ((agreeG x) ⁻¹) (height-<-ε₀ x)

\end{code}
