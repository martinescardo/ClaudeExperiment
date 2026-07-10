# Function extensionality in this repository

This note audits **why function extensionality (funext) is used** in this
repository's Agda code — where it is crucial, and whether it can be avoided. It
covers both `BrouwerOrdinals/` and `DialogueTreeHeight/`. It records a finding,
not a change: nothing in the code was modified.

## `BrouwerOrdinals/`: where funext is used

Every module in `source/Claude/BrouwerOrdinals/` is parameterized by
`fe : Fun-Ext`, but almost all of that is *threading* — passing `fe` on to
imported submodules. Genuine uses of extensionality are exactly **7 sites**, all
the identical idiom

```agda
… (L f) = ap L (dfunext fe (λ n → IH (f n)))
```

in the limit (`L`) case of a `＝`-valued induction:

| Site | Lemma | Statement |
|------|-------|-----------|
| `Orbit.lagda:67` | `⊕-assoc` | `(a ⊕ b) ⊕ c ＝ a ⊕ (b ⊕ c)` |
| `Affine.lagda:88` | `⊗-left-distrib` | `c ⊗ (x ⊕ y) ＝ (c ⊗ x) ⊕ (c ⊗ y)` |
| `Affine.lagda:199` | `⊗-assoc` | `(a ⊗ b) ⊗ c ＝ a ⊗ (b ⊗ c)` |
| `AffineClosure.lagda:52` | `SZ-⊗` | `(S Z) ⊗ y ＝ y`  (left unit, `1 ⊗ y = y`) |
| `Epsilon0.lagda:68` | `Z-left-unit` | `Z ⊕ a ＝ a` |
| `Epsilon0.lagda:191` | `ω^-ι1` | `ω^ ι[ 1 ] ＝ ω` |
| `OmegaPoly.lagda:216` | `ω^⊗` | `ω^ a ⊗ ω^ b ＝ ω^ (a ⊕ b)` |

The last, `ω^⊗`, is the exponent homomorphism `ω^x ⊗ ω^y = ω^(x⊕y)` that the
report highlights as the ω^(-) homomorphism.

Everywhere else, `fe` is only threaded into imports. In particular the
foundational module `Order.lagda` takes `fe` but **never uses it** in its body.

## Why it is needed — the exact mechanism

Brouwer codes have the constructor

```agda
L : (ℕ → 𝓑) → 𝓑
```

and every operation acts pointwise on it:

```agda
a ⊕ L f = L (λ n → a ⊕ f n)
a ⊗ L f = L (λ n → a ⊗ f n)
```

To prove an **equation** whose argument is `L f`, both sides compute to `L g₁`
and `L g₂`, and the induction hypothesis gives `g₁ n ＝ g₂ n` for every `n`.
Concluding `L g₁ ＝ L g₂` (then `ap L`) requires `g₁ ＝ g₂` — i.e. promoting a
*pointwise* equality of the two sequences to an equality of the **functions**.
That promotion is precisely what `dfunext` does. Only the `ℕ → 𝓑` instance is
ever used (universe-monomorphic, `𝓤₀`).

## Can it be avoided?

**Yes in principle — and the code already shows the escape route.** Compare, in
`Orbit.lagda`, the same limit case for two statements:

```agda
⊕-mono-left … (L f) = ≤-L-mono (λ n → ⊕-mono-left p (f n))      -- no funext
⊕-assoc   a b (L f) = ap L (dfunext fe (λ n → ⊕-assoc a b (f n))) -- funext
```

The difference is entirely `≤` vs `＝`. The order `_≤_` (in `Order.lagda`) is an
*inductive relation* whose limit rules consume pointwise families directly:

```agda
≤-ℓ : {a : 𝓑} {f : ℕ → 𝓑} (n : ℕ) → a ≤ f n → a ≤ L f
≤-L : {f : ℕ → 𝓑} {b : 𝓑} → ((n : ℕ) → f n ≤ b) → L f ≤ b
```

so limit cases of `≤` close without funext. Propositional equality `＝` has no
such pointwise limit rule; that is the whole source of the dependency.

The funext requirement therefore comes **solely from choosing to state these
seven laws as propositional equalities on codes containing `L`.** Two ways out:

1. **Principled route.** Replace those `＝`-laws with an inductively-defined
   equivalence `_≈_` (a limit rule taking pointwise `f n ≈ g n`), or with
   two-sided `≤`. Then the `L` cases close by the pointwise constructor,
   funext-free. Cost: the downstream code currently `transport`s along these
   equalities; one would thread `≈` (and its congruences) through those
   rewrites instead. Non-trivial but mechanical.

2. **Keep `＝`, keep funext.** It is a very mild instance, and it genuinely
   *cannot* be discharged — even `ℕ`-funext is not provable in `--without-K`
   MLTT — so if these are wanted as honest equalities at `L`, funext is
   unavoidable.

## `DialogueTreeHeight/`

Of the 69 modules, **67 take `fe : Fun-Ext`**, but again almost all of that is
threading — onto imported `Claude.*` submodules that carry the local lemmas
below. The upstream effectful-forcing modules the main line actually uses
(`MFPSAndVariations.CombinatoryT`, `.Combinators`, `.Dialogue`, `.MFPS-XXIX`,
`.Continuity`) are themselves **funext-free**; see the Discussion. Genuine
`dfunext` applications are **10 sites in 6 files**, in three groups.

### Group 1 — dialogue-tree height (the same limit-case idiom)

The exact `BrouwerOrdinals` phenomenon, now at the dialogue node constructor
`β : (ℕ → B ℕ) → ℕ → B ℕ` and the ordinal limit `L`: the height / operator `H`
of a `β`-node is `L (λ j → S (…))`, so an equality of heights at a node closes
by `ap L (dfunext fe (λ j → …))`.

| Site | Lemma | Statement |
|------|-------|-----------|
| `Constructive.lagda:67` | `height-relabel` | relabelling leaves preserves height: `height (B-functor f d) ＝ height d` |
| `Operator.lagda:62` | `height-is-H` | `height x ＝ H (λ _ → Z) x` |
| `Operator.lagda:76` | `H-kleisli-extension` | `H v (kleisli-extension g d) ＝ H (λ k → H v (g k)) d` |
| `Operator.lagda:94` | `height-iter'` | rewrites the valuation function under `H` |
| `Classical.lagda:87` | `height-relabel` | the same, over **HoTT-book ordinals** (`ap sup`, `_+ₒ 𝟙ₒ`) |

`Classical.lagda` is a deliberately-classical sidecar: it interprets heights
into `Ordinal 𝓤₀`, derives funext from **univalence**
(`Univalence-gives-FunExt`) rather than assuming it, and additionally uses
**excluded middle** (`EM 𝓤₁`, since ordinal successor is not monotone without
it). The constructive main line uses Brouwer codes precisely to avoid this, so
this module does not bear on the main development.

### Group 2 — Brouwer-code arithmetic, re-proved locally

Identical to the `BrouwerOrdinals` idiom (a local copy of the `⊕` unit law):

| Site | Lemma | Statement |
|------|-------|-----------|
| `MultHereditaryH4.lagda:162` | `⊕-Z-left` | `Z ⊕ x ＝ x` |
| `MultHereditaryHM4.lagda:151` | `⊕-Z-left` | `Z ⊕ x ＝ x` (duplicate, in the "HM" fork) |

### Group 3 — System T interpretation agreement (funext on function *values*)

Genuinely different from the limit-case idiom. `MultApplicativeT.agreeF`
certifies that the bespoke fragment's translation into real System T terms
denotes the same thing: `⟦ ⌜ f ⌝F ⟧₁ ＝ ⟦ f ⟧F`. Here the two objects equated
**are functions** (System T functionals), so where the translation is a genuine
`λ` they agree only pointwise — shown by `happly`/`ap` through the applications —
and `dfunext` reassembles the function equality.

| Site | Case | Translation |
|------|------|-------------|
| `MultApplicativeT.lagda:93` | `agreeF (compF f g)` | composition `f ∘ g` |
| `MultApplicativeT.lagda:95` | `agreeF (constF x)` | constant function |
| `MultApplicativeT.lagda:97` | `agreeF (iterDiagF φ G)` | the `S`-diagonal |

The other `agreeF`/`agreeG` cases are `refl` or `ap₂`; funext enters only at
these three genuinely-`λ` translations.

### Can these be avoided?

Groups 1 and 2 have the **same escape route** as `BrouwerOrdinals` — the `≤`
order carries pointwise limit rules, so stating height-invariance and the
arithmetic law as two-sided `≤` (or an inductive `≈`) removes funext; the cost is
that these are naturally *equalities* consumed by `transport` in the majorant
construction, so the change threads downstream. Group 3 needs its own move:
replace the interpretation *equality* `⟦⌜f⌝⟧ ＝ ⟦f⟧` by a pointwise-carried
agreement, or arrange the fragment's interpretation to be *definitionally* the
System T one. Either removes funext there; both are restructurings.

As before, none of the `B`, `kleisli-extension`, `B-functor`, `height`, or `⟦_⟧`
**definitions** need funext (they are plain recursion), and no use is for
propositionality or h-level — every genuine use is congruence/extensionality of
`＝`.

## Discussion

To summarise the audit before reflecting on it: within the `Claude.*` code every
genuine use is a congruence/extensionality of `＝` — the seven limit-case ordinal
equalities in `BrouwerOrdinals/`, and the ten sites in `DialogueTreeHeight/` —
each avoidable only by not using `＝` at a function-typed position. Four short
reflections follow.

### Is funext essential, or incidental?

The two mechanical sources of funext in the `Claude.*` code are the same at
root: a propositional equality `＝` whose two sides are *functions* — sequences
`ℕ → 𝓑` under the `L`/`β` limit constructors, or System T functionals in
`agreeF`. In every case the ingredients are available pointwise, and funext only
reassembles them. Nothing in the *mathematics* — the ordinal rank of a dialogue
tree, the arithmetic of Brouwer codes, the height bound — refers to equality of
functions; that is an artifact of choosing `＝` as the vehicle. The same theorems
can be carried by the order `≤` (which has pointwise limit rules) or by an
inductive equivalence `≈`. So funext here is **incidental to the representation,
not essential to the results**. The honest counterweight: it is a mild,
universe-monomorphic, entirely standard assumption, and removing it is a sizeable
mechanical refactor — re-plumbing every `transport` along these equalities — that
buys little foundational ground. That is why the development simply assumes it.

### How much of this comes from upstream? Almost none

An earlier version of this note claimed the imported TypeTopology machinery was
an irreducible source of funext. That was wrong, and worth correcting. Every
upstream module the **main line** builds on is funext-free: the System T syntax
and combinator interpretation (`MFPSAndVariations.CombinatoryT`, `.Combinators`),
the dialogue datatype with its `B-functor` / `kleisli-extension` (`.Dialogue`),
the MFPS 2013 interpretation (`.MFPS-XXIX`), the continuity definitions
(`.Continuity`), the Brouwer codes (`Ordinals.BrouwerCodes`), and `MLTT.Spartan`.
The 83 `open import UF.FunExt` lines import only the *interface* — the `Fun-Ext`
type — not a use of it.

So the repository's genuine funext usage is essentially **all its own**: the
seven `BrouwerOrdinals/` sites and the ten `DialogueTreeHeight/` sites, each a
local choice to state something as `＝` at a function-typed position. The one
exception is the `Classical.lagda` sidecar, whose HoTT-book-ordinal imports
(`Ordinals.OrdinalOfOrdinals`, `Ordinals.Arithmetic`, `UF.Univalence`, …) pull in
funext (there derived from univalence) together with excluded middle — and that
module is deliberately off the constructive main line (see below).

The consequence is the opposite of what the earlier version said: a funext-free
height development is **within this repository's reach** — reformulate those
local sites — not an upstream project one is blocked on.

### Funext on function values (the `agreeF` phenomenon)

Group 3 of the `DialogueTreeHeight/` audit is worth separating conceptually,
because it is *not* the limit-case idiom. There the function-typed thing is a
*constructor* (`L`, `β`) and funext closes a congruence. In `agreeF` the objects
being equated **are** the functions — two interpretations of the same fragment,
`⟦ ⌜f⌝ ⟧ ＝ ⟦ f ⟧` — and funext does its primitive job: turning extensional
(pointwise) agreement into an identity. This is the version that no reformulation
of *our* datatypes removes; it can be sidestepped only by carrying the agreement
pointwise rather than as `＝` — exactly the route the FSCD / `Internal` work takes
(next subsection) — or by making the fragment's interpretation *definitionally*
the System T one, so that agreement is `refl`.

### A funext-free effectful forcing already exists (FSCD / `Internal`)

The pointwise route is not hypothetical. TypeTopology's
`EffectfulForcing.Internal` development — by Escardó, da Rocha Paiva, Rahli, and
Tosun, described in their FSCD 2025 paper *Internal Effectful Forcing in System
T* — carries out the effectful-forcing translation and its **correctness proof
completely without funext**. The device is `Internal.ExtensionalEquality` (da
Rocha Paiva & Rahli): a type-indexed extensional equality on System T values,

```agda
_≡_ : {A : type} → 〖 A 〗 → 〖 A 〗 → 𝓤₀ ̇
_≡_ {ι}     n₁ n₂ = n₁ ＝ n₂
_≡_ {σ ⇒ τ} f₁ f₂ = {x₁ x₂ : 〖 σ 〗} → x₁ ≡ x₂ → f₁ x₁ ≡ f₂ x₂
```

— `＝` at the base type, a logical relation at function types. Reasoning up to
`_≡_` instead of `_＝_`, one never needs funext to equate functionals; the core
modules (`Internal`, `Correctness`, `External`, `SystemT`, `Subst`,
`ExtensionalEquality`) are `--safe` and funext-free.

This is precisely the Group-3 escape route above, already realized in the
library: `MultApplicativeT.agreeF` — the propositional equality `⟦⌜f⌝⟧ ＝ ⟦f⟧` of
two interpretations — is the analogue of `Internal`'s correctness-up-to-`_≡_`,
and would be funext-free if stated and proved with `_≡_`. (Groups 1 and 2 are a
different matter: they are equalities of *ordinals / Brouwer codes*, not of System
T functions, so they would be discharged by the `≤` / `≈`-on-codes reformulation
rather than by `ExtensionalEquality`.)

**Reference.** Martín H. Escardó, Bruno da Rocha Paiva, Vincent Rahli, and Ayberk
Tosun. *Internal Effectful Forcing in System T.* In 10th International Conference
on Formal Structures for Computation and Deduction (FSCD 2025), LIPIcs vol. 337,
pp. 19:1–19:17, ed. Maribel Fernández, Schloss Dagstuhl – Leibniz-Zentrum für
Informatik, 2025. [doi:10.4230/LIPIcs.FSCD.2025.19](https://doi.org/10.4230/LIPIcs.FSCD.2025.19)

### Constructivity: Brouwer codes vs HoTT-book ordinals

The one place the development reaches past funext is `Classical.lagda`, and it is
instructive. Interpreting heights into the HoTT-book ordinals `Ordinal 𝓤₀`
forces two further assumptions: **univalence** (whence that module's funext is
derived) and **excluded middle** (`EM 𝓤₁`, because ordinal successor is not
monotone there without it). Working instead over **Brouwer codes** — the choice
the report records as deliberate — the successor is monotone by construction, no
EM or univalence is needed, and the only extensionality used is the mild
`ℕ`-funext of the limit case. So the Brouwer-code representation is not a
stylistic preference but the thing that keeps the main line constructive; the
classical module is a sidecar that recovers the standard proof-theoretic reading
at the cost of those axioms.
