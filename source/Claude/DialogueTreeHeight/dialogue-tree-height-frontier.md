# The verified frontier (status after the 2026-06-29 push)

> Canonical exposition: `dialogue-tree-height.md`. Verified tour:
> Agda `DialogueTreeHeight.Index`. This note records, precisely, the
> machine-checked state and the two sub-developments that remain for the
> **first-order** theorem. Honest throughout: the conjecture is open.

## What is now machine-checked (`--safe --without-K`, no postulates)

The tour `DialogueTreeHeight.Index` imports, in dependency order:

1. `…Constructive` — height calculus L1–L3 on Brouwer codes.
2. `…Count` — the `values-≤` Count Lemma (bounded count ⟹ bounded graft).
3. `…Operator` — the operator `H`, composition law, recursor identity
   `height (iter' f x n) = H (λ k → height (fᵏ x)) n`.
4. `…Conditional` — *given* a uniform orbit bound `b`,
   `height (iter' f x n) ≤ b ⊕ height n`.
5. `…Orbit` *(new)* — the **height-side engine**. From a *fixed,
   depth-independent* per-step increment
   `step : height (fᵏ⁺¹ x) ≤ height (fᵏ x) ⊕ c`, it derives the uniform
   orbit bound and hence
   `height-iter-from-step : height (iter' f x n) ≤ (height x ⊕ c ⊗ ω) ⊕ height n`.
   Adds the minimal Brouwer-code arithmetic `ι[_], ω, _⊗_, ⊕-mono-left,
   ⊕-assoc`. This is "depth cannot bootstrap" as a theorem.
6. `…Magnitude` *(new)* — the **value-side**. Oracle-relative magnitude
   `mag-≤ V x := ∀ b α, α ≤[ b ] → dialogue x α ≤ V b`, with propagation
   (`mag-η, mag-succ', mag-generic, mag-kleisli`). `mag-generic` proves the
   oracle resets magnitude to `λ b → b`; `mag-kleisli` is **Lemma R1**, the
   count bound `dialogue n α ≤ V b`.

7. `…Epsilon0` *(new)* — **sub-development (I), complete.** The ε₀
   ordinal-arithmetic library on Brouwer codes: `ω^_`, `tower`,
   `ε₀ = L tower`, `_<_`; the monotonicity toolkit; the inflationary law
   `a ≤ ω^ a`; the strict climb `ω < ω^ ω` and `tower n < ε₀`; the
   absorption `ω^ω ⊗ ω < ε₀`; and the additive closure `⊕-<-ε₀`.
8. `…FirstOrder` *(new)* — **the capstone.** `height-iter-<-ε₀`: the
   first-order recursor height `height (iter' f x n) < ε₀`, given the
   per-step increment `ω^ω` and `height x, height n < ε₀`. Pure assembly of
   (5) and (7).

So both components the two-component analysis calls for are now verified
*as components*: the height engine (5) and the magnitude calculus (6); the
ε₀ accounting (7) is **complete**; and the **first-order recursor case is a
machine-checked theorem (8)** modulo exactly three interface hypotheses,
which sub-development (II) — the term induction — must discharge.

## The two remaining sub-developments (for the first-order theorem)

The first-order theorem — *every closed `t : (ι⇒ι)⇒ι` whose every `Iter` is
at type `ι` has `height (dialogue-tree t) < ε₀`* — now reduces to exactly two
pieces, both standard-shaped, neither yet written:

### (I) The ε₀ ordinal-arithmetic library on Brouwer codes — DONE

Now machine-checked in `DialogueTreeHeight.Epsilon0` (EXIT 0). It defines
`ω^_`, the tower, `ε₀ = L tower`, `_<_`, and proves: the monotonicity
toolkit; the inflationary law `a ≤ ω^ a`; the strict `ω < ω^ ω` and
`tower n < ε₀`; the absorption `ω^ω ⊗ ω < ε₀`; and additive `< ε₀` closure
`⊕-<-ε₀`. The awkward Brouwer-order spots (the `Z ⊕ _` left-unit and the
*successor-of-limit* strictness) were dissolved by a descent
(`tower-strict`) that bottoms out at the proved base `ω < ω^ ω`, and by a
`maxℕ`-to-common-level argument for the additive closure.

### (II) The first-order fundamental theorem — STRUCTURAL CORE DONE

Now machine-checked in `DialogueTreeHeight.Majorant` (EXIT 0). A **height-only**
hereditary majorant suffices at first order (the magnitude component is a
*higher-type* concern — it is needed only for the Part-IV overshoot, which is
a type-level-2 phenomenon; Part II's first-order affine class is purely
ordinal). So:

* `Maj ι = 𝓑`, `Maj (σ⇒τ) = Maj σ → Maj τ`; `R ι x a := height x ≤ a`,
  `R (σ⇒τ) F φ := ∀ x a, R x a → R (F x) (φ a)`.
* Combinator majorants + lemmas `R-Zero/Succ/Ω/K/S` (structural, mirroring
  `MFPS-XXIX.main-lemma`); the ground recursor `R-Iter` with majorant
  `μ-Iter φ a ν = (sup_k φᵏ a) ⊕ ν`, closed via the conditional bound (5),
  the uniform orbit bound being `sup_k φᵏ a` itself.
* First-order syntax = the inductive `T₁` (`Iter` only at `ι`); the
  fundamental theorem `fundamental : (t : T₁ σ) → R σ ⟦t⟧ (μ t)`, giving
  `height ⟦t⟧ ≤ μ t` and the dialogue-tree bound `dialogue-height-≤-μ`.

What remains for the first-order `< ε₀` theorem: **that `μ t < ε₀`** — the
affine-class closure (Part II Lemma A). Module (11) `…Affine` establishes the
key point: this is reachable **without** Hessenberg natural sum. The naive
affine form `a ↦ a ⊗ ι[p] ⊕ d` (constant *outside*) fails to compose, because
the non-commutative `⊗` does **not** right-distribute. But the form
`a ↦ (a ⊕ d) ⊗ ι[p]` (constant *inside*) **does** compose, via the verified
**fold lemma** `affine-fold : x ⊗ ι[p+1] ⊕ d ≤ (x ⊕ d) ⊗ ι[p+1]` together
with `⊗`-associativity and left distributivity (all in plain Brouwer-code
arithmetic). The multiplicative orbit case is closed (`double-orbit-<-ε₀`), and the
**general affine-orbit bound is now proved** (`affine-orbit-<-ε₀`, EXIT 0):
for affine `φ b ≤ (b ⊕ d) ⊗ ι[p+1]` with `d < ε₀`,
`sup_k φᵏ a ≤ (a ⊕ d ⊗ ω) ⊗ ω < ε₀` whenever `a < ε₀` — exactly what `μ-Iter`
consumes. The closure toolkit `AffineClosure` then proves the `ι⇒ι` majorants
that arise are affine and that `Aff` is closed under composition (`Aff-∘`)
and pointwise sum (`Aff-⊕`) — all the building blocks, no postulates.

The single remaining piece is the **hereditary affine closure**: that `μ F`
is affine for every first-order `F : ι⇒ι`. Assembling the toolkit into a
hereditary predicate is genuinely Howard's hereditarily-majorizable
functionals, and the precise obstacle (worked out, not yet overcome) is:

* **ground arguments need a uniform joint bound** (`φ a b ≤ (a⊕b⊕d)⊗ι[m]`
  with `d, m` uniform), because the curried form `(a) → Aff(φ a)` lets the
  affine data vary with `a`, so the `S`-diagonal `λa. φ a (γ a)` cannot be
  bounded;
* **function arguments need a data-dependent transformer** (the result bound
  depends on the argument's affine data — e.g. `μ-Iter g`'s orbit sup depends
  on `g`), which a fixed joint accumulator cannot express (a function argument
  applied `k` times contributes degree `mgᵏ`, `k` unknown to the accumulator);
* moreover `Iter₁ · G : ι⇒ι⇒ι` is **ω-affine in its start argument** (orbit
  sup `≤ (a ⊕ dg⊗ω) ⊗ ω`), so the affine class must also admit `ω` (and `ωᵏ`)
  multipliers, not only finite `ι[m]`.

Reconciling joint-uniform (ground) with data-transformer (function) is now
*done* as a predicate: `Hereditary.𝔅` quantifies the function arguments and
asserts a joint affine bound on the ground arguments relative to a common
upper bound `s` (symmetric, so combining uses associativity not
commutativity). Proved on it: ground extraction `𝔅 ι a ⟺ a < ε₀`, the
argument-shift `JB-shift`, **application closure** `𝔅-app`, and the base
combinators. What is left of the fundamental theorem is `𝔅-K`, `𝔅-S`
(polymorphic inductions on the type) and `𝔅-Iter`.

**The definitive ceiling, however** (found while pushing `𝔅-Iter`): the
finite-`ι[m]`-multiplier affine class caps at `≈ ω^ω` and *cannot* reach
`ε₀`. Nested iteration *from a varying start* — e.g.
`Iter (λx. Iter G x M) X N`, which is first-order (both `Iter` at `ι`) —
makes the iterated function `ω`-affine (`λx. Iter G x N` has orbit-over-start
bound `(x ⊕ d) ⊗ ω`), and iterating an `ω`-affine function climbs the tower
(`ω^ω, ω↑↑n, …`). Bounding this needs `ω^c` multipliers; but `affine-fold`
(`x ⊗ c ⊕ d ≤ (x ⊕ d) ⊗ c`) provably **fails** for limit `c` (`(L g) ⊕ d`
has no single `≤-ℓ` witness when `g`'s base is a limit). So the
constant-inside trick that avoided the natural sum does *not* extend to `ω`.

Conclusion: the natural-sum route is genuinely required, and its **foundation
is now built** (`OmegaPoly`). For the first-order fragment (`< ω^ω`) the
ordinals are ω-polynomials with ℕ coefficients, on which the Hessenberg
natural sum `⊞` is just coefficient-wise addition — manifestly commutative.
With the Horner denotation into Brouwer codes, the key lemma
`poly-key : ⟦p⟧ ⊕ ⟦q⟧ ≤ ⟦p ⊞ q⟧` (and `poly-key'`, the reversed order)
supplies the **commutative upper bound** that the non-commutative `⊕` could
not — the lower-degree terms are absorbed by the higher (`absorb`). All
machine-checked, no postulates.

What remains to finish the first-order `< ε₀` bound: the natural *product*
(polynomial convolution) and `ω^k`; then redo the affine closure with
polynomial-valued majorants (composition uses natural product, which *does*
right-distribute); then the fundamental theorem and relating
`⟦ μ-poly ⟧` back to the dialogue height. The reordering wall is now cleared.

(Caveat on scope: this serves the **first-order** fragment, `< ω^ω`. The full
`ε₀` bound across *all* type levels is Escardó's open conjecture — the tower
to `ε₀` comes from higher-type iteration, which is beyond this development.)

The higher-type recursor (`Iter` at `σ ≠ ι`) is **out of first-order scope**
and is where the climb to `ε₀` proper lives (one `ω`-power per type level);
that is the full conjecture, still open.

## Howard reframing (2026-06-30) — the lever for the *full* conjecture

The dialogue height is the **ordinal rank** of a term's adaptive
oracle-interaction, and Howard's `|System T| = ε₀` dominates such ranks. The
earlier "height ⊥ value ⟹ Howard inapplicable" was a value/rank conflation
(corrected in `Conditional`). So the full conjecture's residual orbit bound is
the dialogue instance of `|T| = ε₀`, splitting as **(A)** magnitude/value
orbit grows `< ε₀` (classical Howard, citable) + **(B)** the bridge
"height-increment `≤ ω^magnitude`" (dialogue-native, via the Count Lemma). The
two-component majorant `…TwoComponent` makes this machine-checked: the
structural combinators are proved in pair form, and the recursor
`R₂-Iter-ground` is exactly the (A)+(B) interface (magnitude = `mag-kleisli` =
Howard (A); height = the conditional bound *given* (B)). This localizes the
*entire* conjecture — all type levels, not just first order — to (B), with (A)
a Howard citation. The affine route capped at `ω^ω` precisely because it
*dropped* the magnitude component that drives the type-level tower.

## Honest status

* New this push (all machine-checked, `--safe`, in the tour): the height
  engine (5), the magnitude calculus (6), the **complete** ε₀ arithmetic
  library (7), and the first-order recursor **capstone** (8)
  `height-iter-<-ε₀`. Plus the re-framing in memory (R3 ⟺ conjecture is not
  peelable; magnitude tracking is forced; the open core splits as (A)
  citable Howard magnitude-growth + (B) the dialogue-native
  height-rides-on-magnitude bridge, whose engine is (5)).
* Sub-development (I) is **done** (the ε₀ arithmetic). Sub-development (II)'s
  **structural core is done** (the first-order fundamental theorem,
  `height ⟦t⟧ ≤ μ t`, module (10)). The first-order `< ε₀` theorem reduces to
  `μ t < ε₀` (the affine-class closure); module (11) shows this needs **only
  plain Brouwer-code arithmetic** — the `affine-fold` lemma makes affine maps
  compose with the constant kept inside, so no Hessenberg natural sum is
  required (a correction to the earlier reading). The multiplicative-orbit
  case is closed; the remainder is routine affine bookkeeping.
* The conjecture remains **open**; nothing here claims otherwise. The
  higher-type case (the climb to `ε₀` itself) is untouched.

---

# The tower frontier (status after the 2026-07 push)

The push above bounds the recursor's *orbit* (`height (iter' f x n) < ε₀`
given a per-step increment). Reaching an unconditional `< ε₀` for **combinatory
System T terms** — the recursor *and* `S` together — was then carried by the
**Howard tower**: a type-indexed predicate `𝕂` (module `…MultHereditaryH`) of
*tracked data*, where an arrow-typed datum is a map plus a *zone pack* — a
joint affine bound `zone ⊗ bumpk (j + JH) (M ⊕ MH)` with a multiplier `M`, a
pool `MH` of consumed function-arguments' multipliers, and a **budget** `j+JH`
(a bump-count) that the recursor's one-`ω`-per-orbit raise spends. The
constraining `PackDom` clause is the *rigid multiplier* invariant: a partial
application's multiplier is `≤ bumpk (budget) (pool)`.

## What the tower machine-checks (`--safe --without-K`, no postulates)

* All base combinators, `K` (fully polymorphic), and the **recursor**
  `GoodH-Iter`, via the orbit engine of `…MultHereditaryG` consuming a pack
  converted to tracked data by `pack-to-Tracked` (which folds the budget into
  the multiplier, `M̂ = bumpk jg Mg`, so the engine can read it).
* The **`S` combinator at all-ground types** — shared, middle and result all
  `ι` — assembled through the diagonal/`pack2`/`packS` chain
  (`…MultHereditaryH8`–`H15`), giving the fragment `TS` an unconditional
  `dialogue-height-<-ε₀`. `TS ⊆ T₃` (`…MultHereditaryFNT`), the all-ground-`S`
  Design-F fragment. This is the recursor *and* all-ground `S`, machine-checked.

## The wall: function-middle `S`

The tower's *unique* target beyond Design F is `S` with a **function-typed
middle** `σ` — where the value `γ a` fed to `φ`'s second slot is itself a
function. This does **not** close, and the reason is now exact.

Feeding the function-value `γ a` costs `jγ` (the middle argument `kγ`'s budget)
**twice** in the diagonal's ground leaf: once in the budget `jδ` (via `γ a`'s
own budget `jkg ≤ jγ`) and once as `jγ` bumps inside the multiplier `Mδ` (via
`γ`'s rigid-multiplier bound `M(γa) ≤ bumpk jγ Mγ`). The outer `pack2`, which
consumes `kγ`, supplies `jγ` **once**. The leaf carries `(m+1)·jγ`, the target
`m·jγ`, for any budget factor `m`: a **`jγ` deficit, scaling-invariant**.

Every uniform escape fails, and for one reason:

* budget scaling (`2×`, the `…MultHereditaryHM*` fork) — scales source and
  target equally; the deficit is invariant;
* budget-folding the value / pre-bumping the pool — **compounds** at the
  diagonal (`γ a`'s multiplier already carries `jγ` bumps, so re-bumping gives
  `2·jγ`);
* restricting to a budget-`0` middle — **vacuous**: `rbb σ 0 0 ≥ 1`, so `K`,
  `S`, `Iter` all have positive budget, and a *function*-typed middle must use
  one of them; no closed term has a budget-`0` function-typed middle.

## Root cause: the recursor ↔ composition tension

All escapes fail identically because the deficit is not a *budget-value*
problem but a *multiplier-capacity* one, and the culprit is a feature the
recursor **requires**:

> The rigid-multiplier clause makes a partial application's multiplier carry
> its budget as bumps. The recursor **needs** this — `pack-to-Tracked` folds
> the budget into the multiplier precisely so the orbit engine can spend it
> (one bump = one orbit raise = one `ω`). Function-middle `S` **fails because
> of it** — that budget-in-multiplier is exactly the extra `jγ` the leaf
> cannot pay.

The recursor requires *multiplier-carries-budget*; composition requires
*multiplier-does-not*. No single flat-multiplier predicate satisfies both.
This is the tower's realization of **one `ω` per type level**: the recursor's
budget-in-multiplier *is* the per-level `ω`, and function-composition cannot
absorb one more level of it. It matches the earlier finding that the frontier
fragments are genuinely *incomparable* (more tracked data ⟹ recursor closes,
`S`-composition fails; less ⟹ vice versa), and it is precisely the canonical
thesis in structural form: *magnitude drives the tower, height rides linearly*.

## The non-tweak direction

Closing this needs the **orbit-count decoupled from the composition-multiplier**
— the orbit engine reads a magnitude-count that function-composition does not
pay. That is the two-component `(height, magnitude)` split (`…TwoComponent`,
proved at first order) **lifted to the hereditary/tower level**, which is the
open kernel (B) itself. So the tower does not stop for a fixable reason: it
stops exactly where the conjecture's own difficulty begins.

* State: the all-ground tower (`TS ⊆ T₃`) is complete and sound. The `2×`
  fork and the fn-middle prototype are documented dead ends, kept as record
  and annotated in-file. Pure Brouwer-ordinal arithmetic was factored out into
  the standalone `BrouwerOrdinals` library. The conjecture remains **open**;
  the frontier is now the hereditary decoupling of orbit-count from
  composition-multiplier — a new architecture, not a tower tweak.
