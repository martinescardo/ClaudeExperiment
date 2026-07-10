# Decoupling orbit-count from composition-multiplier — a design study (2026-07)

> Paper design, no code. Written after the Howard tower reached all-ground `S`
> and hit the definitive function-middle `S` wall (see
> `dialogue-tree-height-frontier.md`, "The tower frontier"). Purpose: work out,
> before writing any predicate, whether the tension that stops the tower can be
> dissolved by separating the two things its `bumpk`-budget conflates. Honest
> throughout, and it does **not** claim to close the conjecture; it locates the
> residual precisely and connects it to the known open kernel (B).

## The tension, restated

The tower leaf is `zone(w) ⊗ bumpk (j + JH) (M ⊕ MH)`. The `bumpk (j+JH)`
factor — the *budget* — carries two unrelated costs at once:

1. **argument-use multiplicity** — how many times a term uses its arguments
   (a genuine ordinal, composes under `⊗`, closed below `ε₀` by `⊗-<-ε₀`);
2. **the recursor's orbit raise** — the depth-independent per-step increment,
   one `ω` per recursor (the additive orbit `a₀ ⊕ c⊗ω`, `Claude.BrouwerOrdinals.Orbit`).

The recursor **requires** (2) to sit in the multiplier (`pack-to-Tracked`
folds it in as `bumpk jg`), and function-middle `S` **fails because of it**:
the middle value `γ a`'s multiplier `≤ bumpk jγ Mγ` carries `γ`'s budget as
bumps, `jγ` appears in the diagonal leaf twice (budget `jδ` and multiplier
`Mδ`), but `pack2` supplies it once. The `jγ` deficit is scaling-invariant
(every uniform bookkeeping fix — `2×`, folding, pre-bumping, affine
restriction — fails identically; see the frontier note).

## The hypothesis and where it holds

**Hypothesis.** If (1) is a genuine ordinal `M < ε₀` composing under `⊗`, with
no `bumpk` budget, then function-middle `S` composes: the diagonal multiplier
is `Mδ = Mφ ⊗ Mγ` (multiplicities multiply), `pack2` consumes `kγ` and gets
`Mγ`, and `Mφ ⊗ Mγ < ε₀`. There is no double-count because ordinal
multiplication is not a two-place bump bookkeeping.

**Where it holds.** For the *multiplicative* part this is real: had the middle
`γ`'s cost been purely a multiplier `Mγ` (as it is for an argument used a
bounded number of times, with no recursor), the diagonal `Mφ ⊗ (Mγ ⊗ ω)`
composes cleanly and `pack2` covers it. The all-ground `S` case is exactly this
and it does close. So the multiplicity axis is *not* the obstruction.

## Where it stops — and this is the real content

Feeding the recursor through the same design shows the hypothesis is
**incomplete**, for a reason that is not bookkeeping. The first-order recursor
is **not** a multiplier; it is affine with a **constant**:

    height (iter' g a n)  ≤  (height a ⊕ (c_g ⊗ ω)) ⊕ height n.

The recursor contributes an *additive constant* `c_g ⊗ ω`, and `c_g` is the
per-step increment of `g` — which for a first-order `g` is `≈ ω^ω`, and which
grows one exponential level per nesting of recursors (this constant tower is
where `ε₀` comes from, not the multiplier). So the tower's `bumpk` budget was
never really tracking multiplicity; it was tracking **this
argument-dependent constant**, folded into the multiplier for uniformity.

That reframes the wall exactly. In `S φ γ a = φ a (γ a)`, when `γ` contains a
recursor, `γ a`'s bound carries a constant `c_γ ⊗ ω` that **depends on `γ`**.
The diagonal `φ (γ a)` must absorb `γ a`'s constant, and doing so hereditarily
— so it composes through `φ`'s own affine structure and stays `< ε₀` — is the
step that fails. The tower encoded that argument-dependent constant as a budget
in the multiplier, which is precisely what produced the scaling-invariant `jγ`
deficit. Decoupling the multiplier does *not* remove the constant; it just
makes visible that the obstruction was the constant all along, not the
multiplicity.

## The architecture the analysis points to

The constant `c_g` is bounded by a **value/magnitude**: `c_g ≤ ω^(magnitude
of g)` (the canonical thesis — the per-step height increment is `ω^` of a
count read off values, never of the depth). This is exactly the
**two-component `(height, magnitude)` split** (`…TwoComponent`, proved at first
order: `R₂ ι x (a,V) = height x ≤ a  ×  mag-≤ V x`):

* the **magnitude** side bounds the argument-dependent constants and is
  **citable Howard** (System T values are hereditarily majorized by
  `< ε₀`-recursive functionals; `iter g a k` is one System T term in `k`) —
  this is component (A);
* the **height** side then composes **linearly** (grafting, Lemma 3: plugging
  a subtree of bounded height costs one `⊕`, regardless of how often it is
  used), with each recursor's increment supplied as `ω^(magnitude)` from the
  magnitude side — this is the bridge (B).

Under this split, function-middle `S` is expected to close: the height of
`φ a (γ a)` is a *linear* (`⊕`) combination of the heights of `φ`, `a`, `γ a`,
with the recursor constants drawn from `ω^(magnitude)` and bounded by Howard.
There is no `⊗` multiplier deficit because the height side does not carry the
orbit constant *as a multiplier* — it carries it *additively*, and the
magnitude carries it *as a value*.

## What is actually open (unchanged, now sharply located)

The residual is the **hereditary** bridge (B1): that a functional's per-step
height increment genuinely is `ω^(its magnitude)`, propagated through higher
types. At first order this is the `c = ω^ω` reading and is within reach (the
frontier note's sub-development (II)). At higher types — where `φ` is a
second-order functional applied to the *function* `γ a` — it is the conjecture's
open core. The tower did not fail for a fixable reason; it failed by encoding
the magnitude-bounded constant as a single-multiplier budget, which cannot
carry a function-typed intermediate's constant compositionally.

**Design conclusion.** Do not build another single-component tower variant. The
next architecture is the two-component predicate made **hereditary**: track
`(height-datum, magnitude-datum)` at every type, let height compose linearly
with recursor increments supplied as `ω^(magnitude)`, and discharge the
magnitude side by hereditary majorization (Howard, component A). The first
concrete, low-risk target is the *second-order* bridge — `φ : (ι⇒ι)⇒ι` applied
to a function `g` — proved consistently (source and target under the same
accounting, the mistake the `2×` line made). Only once that leaf closes on
paper should predicate code be written.

## Status of the codebase this note reasons about

* Complete & sound: all-ground tower (`TS ⊆ T₃`), and the `BrouwerOrdinals`
  arithmetic library (`⊗-<-ε₀`, `Orbit`, `MultOrbit`, `Epsilon0`).
* First-order two-component: `…TwoComponent` (structural cases proved),
  `…Majorant` (first-order fundamental theorem `height ⟦t⟧ ≤ μ t`).
* Documented dead ends (kept as record): the `2×` `HM*` fork, `H18Proto`.
* The conjecture remains open. This note narrows the search to the hereditary
  magnitude→height bridge and rules out the single-multiplier tower family.

---

# The second-order bridge, worked out (2026-07, paper)

Following the note's own recommendation: work `φ : (ι⇒ι)⇒ι` applied to a
function `g`, source and target under the *same* accounting. The result
changes how function-middle `S` should be viewed.

## Height composes additively; the recursor is the only non-linear step

In the dialogue setting, applying `g` inside `φ` is Kleisli grafting, and
Lemma 3 (`height-kleisli-extension`) gives

    height (kleisli g d)  ≤  b_g ⊕ height d,     b_g = a bound on every g-subtree.

The grafted cost `b_g` is added **once** (`⊕`), no matter how many times `φ`
uses `g` — grafting takes the max over leaves, it does not multiply. So every
non-recursor construct (application, `K`, `S`) composes height **linearly**.
The **only** super-linear step is the recursor: `iter g a n = gⁿ a` grafts `g`
*sequentially* `n` times, and the sup over `n` is the additive orbit
(`Claude.BrouwerOrdinals.Orbit`)

    height (iter' g a n)  ≤  (height a ⊕ (c_g ⊗ ω)) ⊕ height n,

contributing one factor `⊗ ω` with a **per-step increment** `c_g` (`g`'s
depth-independent additive constant). Nesting recursors stacks `⊗ ω`s; the
increments `c_g` climb `ω^ω, ω^(ω^ω), …` — the `ε₀` tower lives in the
**increments**, and it is added, never used as a multiplier.

## Function-middle `S` is not a separate obstruction — it is the same bridge

`S φ γ a = φ a (γ a)`. Take the hard shape, where `φ a` iterates its function
argument, `φ a h ≈ iter h b (…)`. Substituting `h = γ a`:

    height (S φ γ a)  ≤  (linear in the heights) ⊕ (c_{γa} ⊗ ω),

where `c_{γa}` is the **increment of `γ a`** — and it appears **once**, as the
recursor's per-step increment. `γ a : ι ⇒ ι` is *first order*, so `c_{γa}` is
bounded by the first-order bridge (`c ≤ ω^(magnitude)`, the `≈ ω^ω` reading).
Everything combines by `⊕` and `⊗ ω`, all `< ε₀`.

**This is the crux the tower obscured.** The middle's cost `c_{γa}` is an
*additive increment*, occurring *once*. The tower encoded it as a `bumpk jγ`
*multiplier*, where it necessarily surfaced in *two* places (the diagonal
budget `jδ` and the multiplier `Mδ`) — the scaling-invariant `2·jγ`-vs-`1·jγ`
deficit was an artifact of turning one additive constant into a multiplicative
budget. Under additive/two-component accounting the constant is single, and
there is no deficit. Function-middle `S` is then **not** a distinct hard case:
it is subsumed by the ordinary magnitude→increment bridge, no worse than the
recursor whose function argument it supplies. (This matches, and sharpens, the
Design-F reading that the diagonal's affine data must *depend on* the fn-arg's
data: the dependence is exactly "the increment `c_{γa}` comes from `γ`," which
the magnitude component tracks and which a fixed-data predicate cannot.)

## The concrete, possibly-reachable target

The analysis suggests a target the tower could not touch but the two-component
route might, using only machinery that already exists at first order:

> **First-order function-middle `S` via a hereditary two-component predicate.**
> Track `(height-affine-datum, magnitude)` at each type. Height composes by
> `⊕` (grafting) with `⊗ ω` per recursor (`Orbit`); each recursor's increment
> is supplied as `ω^(magnitude)` (first-order bridge, `c ≈ ω^ω`, within reach);
> the magnitude side is discharged by hereditary majorization (`…Magnitude`,
> Count Lemma, Howard — component A). Because the middle `γ a` is first order,
> only the *first-order* increment bound is needed, even though `φ` is
> second order.

Caveats, held honestly (the `2×` line is a warning): (i) this is a paper
reduction, not a proof — the hereditary two-component predicate has not been
written, and setting up its `S`/`app` cases so height stays affine while the
magnitude discharges the increments is exactly the work; (ii) the claim
"`φ a` iterates a first-order `γ a`, so first-order increments suffice" must be
checked for *all* second-order `φ`, not just the recursor shape — a `φ` that
feeds `γ a` into another function-typed slot could raise the type level; (iii)
the general (higher-type) bridge (B1) remains the open core and is untouched.

## Design conclusion (updated)

Do **not** build a fn-middle `S` pack in any single-multiplier tower — the
deficit is intrinsic to multiplicative budget encoding. Build the **hereditary
two-component predicate** and get fn-middle `S` *for free* from the increment
bridge, first at first order (increment `≈ ω^ω`, reachable) and only then at
higher types (the open kernel). Before writing it, verify caveat (ii) on paper:
enumerate the second-order combinator shapes and confirm each keeps the middle
value first order (or identify which raise the level, isolating exactly the
higher-order residual).

## Confirmed against the code — caveat (ii) resolves for `T₁`

Checked the fragment the whole first-order theorem targets, `Majorant.T₁`:

* `Iter₁ : T₁ ((ι⇒ι)⇒ι⇒ι⇒ι)` — the recursor is **fixed at ground type**.
  Every recursor in a `T₁` term iterates a *first-order* function, so every
  increment is a first-order increment (`c ≈ ω^ω`). There is no higher-order
  recursor in `T₁` to raise the level. Caveat (ii) is void here.
* `S₁ : {ρ σ τ} → T₁ (…)` — `S` is polymorphic, so **function-middle `S` is
  already a `T₁` term**.
* `fundamental : (t : T₁ σ) → R σ ⟦t⟧₁ (μ t)` — the height majorant
  `height ⟦t⟧₁ ≤ μ t` is **already proved for all of `T₁`, including
  function-middle `S`** (`R-S`, `Majorant`).

So for `T₁`: the fn-middle `S` height bound is *done*; the entire residual is
`μ t < ε₀`, and because every recursor is first order, that residual is the
**first-order magnitude→increment bridge** — exactly what the rest of `T₁`
needs. Function-middle `S` adds **no new open problem** at first order.

**This retires the tower framing.** The tower spent modules 45–66 (and this
session's `HM*` fork) trying to bound `μ(S φ γ) < ε₀` for fn-middle `S` by a
single-multiplier hereditary predicate, and hit a self-inflicted deficit. The
right route was never a bespoke fn-middle pack: it is the uniform first-order
`μ t < ε₀` argument for `T₁` — the hereditary two-component / affine closure
with recursor increments bounded by `ω^(magnitude)` — which delivers fn-middle
`S` for free. That closure at *second order* (`μ φ` affine in the function
argument's data, discharged by the magnitude component rather than fixed data)
is the concrete unfinished piece; it is first-order in the recursors and so
sits below the genuine open kernel (B1) at higher types.

## Net (paper session)

* Function-middle `S` is **not** a separate obstruction; the tower's deficit
  was an artifact of multiplicative budget encoding. Additively (two-component),
  the middle's increment appears once.
* For `T₁`, `height ⟦t⟧ ≤ μ t` is proved *including* fn-middle `S`; the residual
  is the uniform first-order `μ t < ε₀`.
* Concrete next target (paper → code): the **second-order affine/increment
  closure** — `μ` of a second-order functional bounded `< ε₀`, its function
  argument's increment supplied by the magnitude side — completing `μ t < ε₀`
  for `T₁`. This is first-order in the recursors and does **not** require the
  higher-type bridge (B1).
* Do not resume the tower's fn-middle packs.

---

# Stratify by iterator level and induct on `n` (2026-07, paper; Escardó's steer)

Logical relations for *full* `T` stumble because the iterators increase
dialogue strength with type level — a single hereditary predicate has no
uniform top (this is what broke the Howard tower at fn-middle `S`). The move:
**do not build one predicate; stratify.** Let `Tₙ` = System T with iterators
of type level `≤ n`. Prove `Tₙ`'s dialogue height `< bₙ` by a logical relation
`Rₙ` (bounded strength, so tractable), then induct on `n`, `sup bₙ = ε₀`. The
type-level tower is handled *outside* the relation, by the induction on `n`.

The induction step is exactly **CSL 2011 (Escardó–Oliva–Powell), `Pₙ ⟺
T_{n+1}`**: a level-`n+1` iterator is a finite product of level-`n` selection
functions — a finite sequential game whose moves are level-`n`, bounded by the
IH — so stripping one iterator level costs one `ω`-exponential:
`b_{n+1} = ω^{bₙ}`-ish. "One `ω` per type level" becomes a recursion on `n`.

**The `S`/`K` worry resolves.** `S`, `K`, application are *structural*: height
composes additively (grafting, Lemma 3, one `⊕` per plugged subtree,
independent of type level), and they do not loop. Only iterators loop and feed
the orbit `⊗ ω`. So a `Tₙ` term may carry `S`/`K` at arbitrarily high level,
but those add only finite structural height — they cannot manufacture
higher-level *iteration* (the hierarchy is strict). The ordinal bound `bₙ` is
set entirely by the level-`≤n` iterators; `S`/`K` pass it through at every
level. They must be *interpreted* hereditarily (Tait fundamental theorem) but
do not move the ordinal.

**fn-middle `S` closes with genuine-ordinal data.** The `(m+1)·jγ`-vs-`m·jγ`
deficit was an artifact of the tower's `bumpk`-budget encoding (one additive
constant surfacing twice). With genuine ordinal data the diagonal constant is

    d_δ  =  m_φ ⊗ d_{γa}  ⊕  d_φ

— `φ` uses the middle value `m_φ` times, each costing `γ a`'s constant, plus
`φ`'s own. Each piece `< ε₀` and `≤ bₙ` (both `φ`, `γ ∈ Tₙ`); `ε₀` is closed
under `⊕`, `⊗`; `d_{γa}` appears **once**. Design F failed here (fixed data
cannot depend on the argument's `d`); the tower failed (tracked data,
mis-encoded as a multiplicative budget). A stratified relation whose data are
genuine ordinals — constants allowed to depend on the argument's constant,
composing by `⊕`/`⊗`, all `≤ bₙ` — sidesteps both.

## The strategy

1. `Rₙ` at all types; data = genuine-ordinal affine transformers
   (`b ↦ (b ⊕ d) ⊗ m`, `d` a function of the argument's `d`), ordinals `< bₙ`.
2. `S`/`K`/app: structural, preserve `Rₙ` at every level, height-linear.
3. Iterators (level `≤ n`): increment `≤ b_{n-1} ⊗ ω`, via recursor→product +
   IH.
4. Induction on `n`: `bₙ = ω^{b_{n-1}}`-ish, `sup = ε₀`.

**Why this is more tractable than everything before.** The second-order bridge
no longer has to hold for *arbitrary* increment (the open kernel) — only for
increment `≤ bₙ`, `n` fixed; the unboundedness is discharged by the outer
induction. Bounded-increment second-order composition is a much smaller target.

Caveats, held: (i) step 1's data class needs the right closure — richer than
Design F's fixed data, without the tower's multiplicative budget; the `S`-case
transformer composing and staying affine is the real content (work the leaf
*consistently* before code — the `2×` warning); (ii) step 3 needs the
product's dialogue height bounded by the orbit (plausible — it *is* a finite
orbit — unchecked); (iii) "`S`/`K` height-linear at all levels" is the
hereditary Lemma 3 — solid at ground, and the function-typed-subresult
(second-order) version is the piece to verify, now with the increment
*bounded* by `bₙ`, which is what should make it go through.

## Next paper step

Work the **bounded-increment second-order bridge**: `φ : (ι⇒ι)⇒ι` applied to
a function `g` with constant `d_g ≤ bₙ`, show `height(φ g) ≤ (affine in d_g,
m_g) ⊕ (φ's constant ≤ bₙ)`, source and target under the *same* accounting.
If it closes on paper with the bounded `d_g`, that is the `Rₙ` fn-middle `S`
case, and the strategy is ready to prototype (`Rₙ` for small `n`, e.g. the
ground-iterator fragment, first).

---

# The data class, made precise (2026-07, paper) — genuine-ordinal affine transformers

The three attempts, side by side:

* **Design F** (`MultHereditaryF…`): data is a *fixed* pair `(d, m)`,
  `φ b ≤ (b ⊕ d) ⊗ ι[m]`. Fails fn-middle `S`: the diagonal's `d` must
  *depend on the middle's* `d`, which fixed data cannot express.
* **Howard tower** (`MultHereditaryH…`): data depends on the argument, but the
  recursor's raise is a `bumpk`-budget (a bump-*count*) — which surfaces the
  middle's cost twice (`jδ` and `Mδ`), the scaling-invariant deficit.
* **This proposal**: data depends on the argument *as genuine ordinals*, and
  the recursor's raise is supplied by the orbit engines (`AffineOrbit`,
  `MultOrbit`) as a real ordinal factor — no budget, no count.

## The class

Hereditary affine predicate `Aff σ` on the majorant `Maj σ` (`Majorant.Maj`):

    Aff ι a          := a < ε₀
    Aff (σ⇒τ) φ      := (∀ g, Aff σ g → Aff τ (φ g))      (hereditary)
                       ∧  φ is affine-transforming:
                          its output ordinal data is an ordinal-arithmetic
                          function of the input's — built only from
                          ⊕, ⊗, ω^(·), and the orbit closures — hence < ε₀.

Concretely at the two levels that matter for `T₁`:

* first order (`ι⇒ι`): `Aff φ ⟺ ∃ d m < ε₀. φ a ≤ (a ⊕ d) ⊗ ι[m]` (Design F's
  `Aff`, reused verbatim);
* second order (`(ι⇒ι)⇒ι`): `Aff φ` carries a **transformer**
  `D : (first-order data) → 𝓑` with `φ h ≤ D(d_h, m_h)` and
  `D(d,m) = c₀ ⊕ c₁ ⊗ d ⊕ c₂ ⊗ (ω^(m ⊗ ω))` (constants `cᵢ < ε₀`). `D` is the
  genuine-ordinal analogue of the tower's tracked data.

## Case 1 — the iterator (via the existing orbit engines, no budget)

`μ-Iter φ a ν = L(λk. iter φ a k) ⊕ ν`. For first-order `Aff φ` with `(d, m)`:

* `m = 1`: `L(λk. φᵏ a) ≤ a ⊕ (d ⊗ ω)` — `Orbit.orbit-sup-≤` / `AffineOrbit`.
* `m > 1`: `L ≤ a ⊗ ω^(m ⊗ ω)` — `MultOrbit.orbit-mult-<-ε₀`.

Either way `< ε₀`, affine in `a, ν`, and — reading `μ-Iter` as a second-order
object in its function argument — its transformer is
`D_Iter(d, m) = d ⊗ ω` (additive) or `ω^(m ⊗ ω)` (multiplicative). A genuine
ordinal function of `(d, m)`; **no `bumpk`, no budget.** The recursor's
one-`ω`-per-level enters here, as an ordinal factor, exactly where the tower
inserted a bump-count.

## Case 2 — function-middle `S` (the case that broke the tower)

`μ-S φ γ a = φ(a)(γ(a))`. Here `φ(a)` is a *second-order* majorant with
transformer `D` (Case-1-style), and `γ(a)` is a *first-order* affine map with
data `(d_{γa}, m_{γa}) < ε₀` (from `Aff γ`, `γ ∈ T₁`). Then

    μ-S φ γ a = D(d_{γa}, m_{γa})
              = c₀ ⊕ c₁ ⊗ d_{γa} ⊕ c₂ ⊗ ω^(m_{γa} ⊗ ω)  <  ε₀.

`d_{γa}` occurs **once**, with `φ(a)`'s coefficient; every constant `< ε₀`;
`ε₀` closed under `⊕, ⊗, ω^`. **Closes — no deficit.** The tower produced the
same quantity but written multiplicatively with a bump-count, where the single
`d_{γa}` had to be paid twice.

## What remains to check (paper), then prototype

* Base combinators (`K`, `Ω`, `Succ`, `Zero`) carry `Aff` — routine (Design F
  has these).
* `μ-app` composes transformers — first order is Design F's `Aff-∘`; the
  second-order composition (a transformer fed a transformer's output) is the
  new lemma; ordinary ordinal arithmetic (`⊕, ⊗, ω^`), expected to go through,
  but the piece to write *consistently* before code.
* Then `Aff` at `ι` gives `μ t < ε₀` for every `T₁` term, **including
  fn-middle `S`** — completing the first-order theorem the tower could not.

Prototype order (small, checkable, each verified before the next): (1) the
second-order transformer type and its `⊕/⊗/ω^` closure lemmas (reuse
`Epsilon0`, `AffineOrbit`, `MultOrbit`); (2) `Aff-Iter` (Case 1) and
`Aff-S`-fn-middle (Case 2) as standalone lemmas; (3) the `Aff` predicate +
fundamental theorem over `T₁`. No tower, no `bumpk`.
