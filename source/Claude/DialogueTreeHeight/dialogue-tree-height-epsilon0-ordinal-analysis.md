# The ε₀ bound for dialogue-tree heights: the ordinal analysis

> **Working note (superseded).** Canonical, corrected account:
> **`dialogue-tree-height.md`**. Verified core: Agda `DialogueTreeHeight.Index`.
> Kept as record; note the attribution correction below and in
> `dialogue-tree-height-correct-framing.md`.

*This is the promised "real §6": an attempt at a genuine proof that
`h(dialogue-tree t) < ε₀` for every System T term `t : (ι⇒ι)⇒ι`, going
beyond the sketch in `dialogue-tree-height-epsilon0.md`. It is honest
about what closes and what does not.*

> **⚠ Status update (after a real attempt at obligation (†) — see Part IV).**
> The "run at (†)" turned up a structural obstruction that invalidates the
> *strategy* of Parts I–III as a route to the **strict** bound, though it
> leaves the elementary lemmas and the first-order theorem intact. In one
> line: **the height-only majorant of Part I provably over-estimates to
> `ε₀`** (there is an explicit closed term with majorant exactly `ε₀` whose
> true height is finite), because `Φ_σ` replaces every iteration count by
> `ω`. So `μ(s) < ε₀` is *false* for some `s`, and "reduce to `μ < ε₀`" is
> not a usable reduction. Read Parts I–III as a correct but non-strict
> upper bound (`h ≤ μ`, and `μ ≤ ε₀` only after the fact), and Part IV for
> the corrected picture and the genuine framework needed (Howard
> majorizability tracking magnitude *and* height). I have **not** proved the
> conjecture.

**Bottom line.** The conjecture is **true**. Two of the three parts are
complete and self-contained:

* **Part I** (the *reduction*) reduces the conjecture to a pure statement
  about ordinal-valued majorants, with a fully rigorous fundamental
  theorem. This is the genuinely new, dialogue-specific content.
* **Part II** proves the bound **completely for the first-order fragment**
  (all `Iter`s at type `ι`, i.e. the primitive-recursive-in-the-oracle
  terms), via a clean ordinal-arithmetic closure lemma.
* **Part III** (the full higher-type case) is where the difficulty
  genuinely lives. I give the invariant that should close it (`𝒫`), prove
  its ground closure, isolate the *exact* remaining obligation, and
  explain why that obligation is precisely the classical ordinal analysis
  of Gödel's T (Howard 1970). Modulo that standard result the conjecture
  is established; a complete from-scratch verification of the higher-type
  bookkeeping is **not** finished here, and I do not claim it.

Throughout I use these standard facts about ε₀ without proof: ε₀ is
closed under ordinal `+`, `·`, `a ↦ ω^a` and `(a,b) ↦ a^b`, and under the
commutative *natural* (Hessenberg) sum `⊕` and product `⊗`; moreover
`ω^{a⊕b} = ω^a ⊗ ω^b`, `⊗` distributes over `⊕`, `a ⊗ 1 = a`, and
`a ↦ ω^a` is continuous (`ω^{sup} = sup ω^{·}`). These are textbook
(e.g. via Cantor normal form).

---

## Part 0. Recap

Height `h : B ℕ → Ord`: `h(η n) = 0`, `h(β φ i) = sup_n (h(φ n) + 1)`.

Dialogue semantics `B⟦_⟧` of combinatory System T with oracle (file
`MFPS-XXIX.lagda`): `ι ↦ B ℕ`, `σ⇒τ ↦ B-Set⟦σ⟧ → B-Set⟦τ⟧`; `Zero ↦ η 0`,
`Succ ↦ succ' = B-functor succ`, `Ω ↦ generic`, `K ↦ Ķ`, `S ↦ Ş`,
`Iter ↦ iter' = λ f x. Kleisli-extension (iter f x)`, application ↦
application. For `t : (ι⇒ι)⇒ι`, `dialogue-tree t = B⟦embedding t · Ω⟧`.

The three elementary lemmas (formalised in `DialogueTreeHeight.*`):

* **L1** `h(B-functor f d) = h(d)` (relabelling is height-free).
* **L2** `h(generic d) ≤ h(d) + 1`.
* **L3** `h(g k) ≤ b` for all `k` ⟹ `h(kleisli-extension g d) ≤ b + h(d)`.

---

## Part I. Majorization and the fundamental theorem (complete)

### I.1 Majorants

For each type `σ` define a set `M_σ` of *majorants* with a preorder `≤`:

* `M_ι = Ord`, with the ordinal order.
* `M_{σ⇒τ} =` monotone functions `M_σ → M_τ`, ordered pointwise.

Define the **majorization relation** `R_σ ⊆ B-Set⟦σ⟧ × M_σ`:

* `R_ι(x, m) :⟺ h(x) ≤ m`.
* `R_{σ⇒τ}(F, φ) :⟺ ∀ x a. R_σ(x,a) → R_τ(F x, φ a)`.

**Upward closure.** `R_σ(x,a)` and `a ≤ a'` imply `R_σ(x,a')`. *(Induction
on `σ`; ground is transitivity of `≤`, function case is pointwise.)*

For `M_σ` we take **pointwise suprema** of ℕ-indexed families; then if
`R_σ(x, a_k)` for all `k` then `R_σ(x, sup_k a_k)` (by upward closure,
since `a_k ≤ sup a_k`).

### I.2 The higher-type grafting lemma

> **Lemma G.** Suppose `R_σ(g k, c_k)` for all `k`, and `h(n) ≤ ν`. Then
> `R_σ(Kleisli-extension g n, (sup_k c_k) ▷ ν)`,
>
> where for `m ∈ M_σ` and an ordinal `ν`, `m ▷ ν ∈ M_σ` is defined by
> `m ▷ ν = m + ν` (ordinal sum) at `ι`, and `(m ▷ ν) a = (m a) ▷ ν` at
> `σ⇒τ`.

*Proof.* Induction on `σ`.

*Ground.* `Kleisli-extension = kleisli-extension`; with uniform bound
`b := sup_k c_k` we have `h(g k) ≤ b` for all `k`, so by **L3**
`h(kleisli-extension g n) ≤ b + ν = (sup_k c_k) ▷ ν`.

*Step `σ⇒τ`.* Take `R_σ(y,b)`. By definition
`Kleisli-extension g n y = Kleisli-extension (λk. g k y) n`. From
`R_{σ⇒τ}(g k, c_k)` and `R_σ(y,b)` we get `R_τ(g k y, c_k b)`. By the IH
at `τ`, `R_τ(Kleisli-extension (λk. g k y) n, (sup_k (c_k b)) ▷ ν)`. Since
sups are pointwise, `sup_k (c_k b) = (sup_k c_k) b`, and
`((sup_k c_k) b) ▷ ν = ((sup_k c_k) ▷ ν) b`. ∎

### I.3 Combinator majorants and the fundamental theorem

Assign a majorant to each combinator:

| `c` | `μ(c)` | witnessing `R(B⟦c⟧, μ(c))` |
|---|---|---|
| `Zero` | `0` | `h(η 0)=0` |
| `Succ` | `a ↦ a` | **L1** |
| `Ω` | `a ↦ a+1` | **L2** |
| `K` | `a ↦ b ↦ a` | immediate |
| `S` | `φ ↦ γ ↦ a ↦ φ a (γ a)` | immediate |
| `Iter` | `Φ` (below) | Lemma I.4 |

and for application set `μ(t·u) = μ(t) μ(u)`; `R` is preserved by
application by definition of `R_{σ⇒τ}`. For the K and S rows one checks
the defining implication of `R` directly, exactly as in the `main-lemma`
of `MFPS-XXIX.lagda` (this relation is that proof's `R`, with `h(·) ≤ ·`
in place of `decode`).

The iteration majorant, for `Iter : (σ⇒σ)⇒σ⇒ι⇒σ`, is

> `Φ := λ φ. λ a. λ ν.  φ^{(ω)}(a) ▷ ν`,  where `φ^{(ω)}(a) := sup_{k<ω} φ^k(a)`  (pointwise in `M_σ`).

> **Lemma I.4.** `R_{(σ⇒σ)⇒σ⇒ι⇒σ}(iter', Φ)`.

*Proof.* Assume `R_{σ⇒σ}(f,φ)`, `R_σ(x,a)`, `R_ι(n,ν)` (i.e. `h(n) ≤ ν`).
By induction on `k`, `R_σ(f^k x, φ^k a)` (base `R_σ(x,a)`; step uses
`R_{σ⇒σ}(f,φ)`). Since `φ^k a ≤ φ^{(ω)} a`, upward closure gives
`R_σ(f^k x, φ^{(ω)} a)` for **all** `k`. Now `iter' f x n =
Kleisli-extension (iter f x) n` with `(iter f x) k = f^k x`, so Lemma G
(with the uniform majorant `c_k := φ^{(ω)} a`) yields
`R_σ(iter' f x n, φ^{(ω)}(a) ▷ ν)`. ∎

Putting these together by induction on terms:

> **Fundamental Theorem.** For every closed term `s : σ`,
> `R_σ(B⟦s⟧, μ(s))`, where `μ(s)` is the compositional majorant above.

### I.4 The reduction

Apply the Fundamental Theorem to `embedding t · Ω`. With `R_{ι⇒ι}(generic,
(a↦a+1))` (L2) we obtain, for `t : (ι⇒ι)⇒ι`,

> `h(dialogue-tree t) ≤ μ(embedding t) (a ↦ a+1) ∈ Ord`.

Hence:

> **Reduction Theorem.** The conjecture holds iff for every closed `s : ι`,
> `μ(s) < ε₀` — equivalently, the majorant calculus built from
> `{0, id, (a↦a+1), K, S}` under application and the iteration combinators
> `Φ_σ` produces only ground values `< ε₀`.

This part is complete and rigorous. The only nontrivial operation in the
calculus is `Φ_σ`, whose sole non-elementary ingredient is the
**ω-orbit supremum** `φ ↦ φ^{(ω)}`. Everything now is ordinal arithmetic.

---

## Part II. The first-order fragment (complete)

Call a term **first-order** if every `Iter` in it is at type `σ = ι`
(so `Φ` is only ever used at ground, where `▷ ν = + ν`). These are exactly
the primitive-recursive-in-the-oracle terms.

Define the **affine class**

> `𝒜 := { f : Ord→Ord monotone : ∃ c, δ < ε₀ ∀a, f(a) ≤ (a ⊗ ω^c) ⊕ δ }`.

> **Lemma A (closure of `𝒜`).** `𝒜` contains `0, id, (a↦a+1)` and all
> constants `< ε₀`, and is closed under (i) composition, (ii) `f ↦ (a ↦
> f(a) + ν)` for `ν < ε₀`, and (iii) the orbit-sup `f ↦ f^{(ω)}`.
> Moreover every `f ∈ 𝒜` maps ordinals `< ε₀` to ordinals `< ε₀`.

*Proof.* Membership of generators: `id` has `c=δ=0` (`a ⊗ 1 = a`); `a↦a+1`
has `c=0, δ=1` (`a+1 ≤ a ⊕ 1`); a constant `δ₀` is `≤ a ⊕ δ₀`. The final
clause is closure of ε₀ under `⊗, ω^·, ⊕`.

(i) If `f(a) ≤ (a⊗ω^c)⊕δ` and `g(a) ≤ (a⊗ω^{c'})⊕δ'`, then using
distributivity and `ω^{x}⊗ω^{y}=ω^{x⊕y}`,
```
f(g(a)) ≤ (g(a) ⊗ ω^c) ⊕ δ
        ≤ ((a⊗ω^{c'}) ⊕ δ') ⊗ ω^c ⊕ δ
        = (a ⊗ ω^{c'⊕c}) ⊕ (δ'⊗ω^c) ⊕ δ,
```
so `f∘g ∈ 𝒜` with `c'' = c'⊕c`, `δ'' = (δ'⊗ω^c)⊕δ`, both `< ε₀`.

(ii) `f(a)+ν ≤ f(a)⊕ν ≤ (a⊗ω^c)⊕(δ⊕ν)`.

(iii) By induction `f^k(a) ≤ (a⊗ω^{γ_k})⊕δ_k` with `γ_{k+1}=γ_k⊕c`
(`γ_k = c⊗k`) and `δ_{k+1}=(δ_k⊗ω^c)⊕δ`, `δ_0=0`; each `γ_k,δ_k<ε₀`. Then
```
f^{(ω)}(a) = sup_k f^k(a) ≤ sup_k [ (a⊗ω^{c⊗k}) ⊕ δ_k ]
          ≤ (a ⊗ ω^{c⊗ω}) ⊕ Δ,
```
where `Δ := sup_k δ_k`. Indeed each summand is `≤ (a⊗ω^{c⊗ω})⊕Δ` because
`c⊗k ≤ c⊗ω` and `δ_k ≤ Δ`; and `c⊗ω < ε₀`, `Δ ≤ δ⊗ω^{c⊗ω}·ω < ε₀`. So
`f^{(ω)} ∈ 𝒜`. ∎

> **Theorem II.** Every first-order closed `s : ι` has `μ(s) < ε₀` (indeed
> `< ω^{ω^{ω}}`-ish; the bound is `ε₀`-safe). Hence `h(dialogue-tree t) <
> ε₀` for first-order `t`.

*Proof.* The majorant of every first-order subterm, read as a function of
its `ι`-arguments, lies in (a finitely-many-variable version of) `𝒜`. The
generators `Zero, Succ(id), Ω(+1), K, S` and application stay in `𝒜` by
Lemma A(i) and the closure under the cartesian/structural manipulations of
`K, S` (which only compose and project). Ground `Iter` contributes
`Φ_ι(φ)(a)(ν) = φ^{(ω)}(a) + ν`, which is in `𝒜` by Lemma A(iii) and (ii)
whenever `φ ∈ 𝒜`. Evaluating the closed ground term gives a value
`≤ (0 ⊗ ω^c) ⊕ δ = δ < ε₀`. ∎

The multivariate bookkeeping for `K`/`S` is routine (each combinator is a
projection/composition, under which the affine bound is stable); the
mathematical content is Lemma A, which is fully proved.

---

## Part III. The general case (invariant identified; closure not finished)

For the full calculus, `Φ_σ` is used at higher types. The orbit-sup is
then **pointwise in a function space**, and the danger is concrete:

> `𝒜` is *not* closed under orbit-sup once we leave it. If some ground
> majorant were as large as `a ↦ ω^a`, then iterating it (ground `Iter`
> with an oracle-unbounded count `n`) would give
> `sup_k (ω^{ω^{...^a}}) = ε₀`, **violating the conjecture**.

So the whole theorem rests on: **no System T ground majorant is that
large.** Part II shows first-order majorants are affine (`𝒜`), hence safe.
The question is whether *higher-type* iteration can manufacture a ground
function with exponential growth in the *degree*.

### III.1 The proposed invariant `𝒫`

Writing `a = ω^d` (Cantor), the relevant measure of a ground majorant `f`
is how it transforms the **degree** `d`. Affine `f(a)=(a⊗ω^c)⊕δ` transforms
`d ↦ d⊕c` (additive). Analysis of depth-2 iterations (iterating a
function that itself uses `y` as a count) produces, e.g., `a ↦ a^{ω}`,
which transforms `d ↦ d·ω` (multiplicative — *not* affine). The general
safe class appears to be "polynomial in the degree":

> `𝒫 := { f : ∃ c,e,δ < ε₀ ∀a, f(a) ≤ (a^{ω^c} ⊗ ω^e) ⊕ δ }`
>     ( degree transform `d ↦ (d · ω^c) ⊕ e` ).

> **Lemma P (ground closure of `𝒫`).** `𝒫 ⊇ 𝒜`, maps `< ε₀` to `< ε₀`,
> and is closed under composition, `+ν`, and orbit-sup.

*Proof sketch (the computations mirror Lemma A).* For orbit-sup of
`f(a)=a^{ω^c}`: `f^k(a) = a^{(ω^c)^k} = a^{ω^{c·k}}`, so
`f^{(ω)}(a) = a^{ω^{c·ω}}` with `c·ω < ε₀` — still in `𝒫`. Composition:
`(a^{ω^{c'}})^{ω^c} = a^{ω^{c'}·ω^c} = a^{ω^{c'⊕c}}`. The `ω^e, δ` factors
are absorbed as in Lemma A. The key point is that the orbit-sup keeps the
degree-transform **multiplicative** (`d ↦ d·ω^{c'}`); it never becomes
**exponential** (`d ↦ ω^d`), which is the only thing that would reach ε₀.∎

So `𝒫` is closed under everything that happens *at ground*. If one proves
all ground System T majorants lie in `𝒫`, the conjecture follows.

### III.2 The exact remaining obligation

To prove "all ground majorants `∈ 𝒫`" one must propagate a suitable
invariant **through higher types**, i.e. define `𝒫_σ ⊆ M_σ` (with
`𝒫_ι = 𝒫`) and prove:

> **(†)** `K, S` preserve `𝒫_•`; application preserves `𝒫_•`; and for every
> `σ`, `Φ_σ` maps `𝒫_{σ⇒σ} × 𝒫_σ × 𝒫_ι` into `𝒫_σ`.

The crux is the `Φ_σ` clause for **function types** `σ`. There the orbit-sup
is a pointwise sup of *functionals*, and one must show the iterated
functional, applied to arguments, still yields ground values whose
degree-transform stays multiplicative. Intuitively this should hold,
because producing an *exponential* degree-transform `d ↦ ω^d` would require
iterating a functional whose own effect is already super-polynomial, which
by induction does not arise — each type level adds one "Grzegorczyk step"
to the polynomial degree, and a fixed term has finite type level, hence a
fixed `c < ε₀`. **But I have not verified (†) at function types.** Defining
`𝒫_σ` so that it is simultaneously (a) preserved by `K, S`, application, and
`Φ_σ`, and (b) restrictive enough at `ι` to give `𝒫`, is exactly the
delicate, error-prone heart of the matter, and I do not have a checked
proof of it.

### III.3 Why this is the ordinal analysis of T, and why the conjecture holds

Obligation (†) is not an isolated curiosity: it is a form of the **ordinal
analysis of Gödel's System T**. Howard (1970), *Assignment of ordinals to
terms for primitive recursive functionals of finite type*, assigns to each
closed term of T an ordinal `< ε₀` by exactly such a hereditary,
type-indexed bound, and the bound is preserved by application and by the
recursor at every type — which is (†) in the form needed here. The
dialogue-tree height is a particular, and *no larger*, such measure: by
**L1–L3** every step of `B⟦_⟧` changes height only additively/by grafting,
so `h(dialogue-tree t)` is dominated by Howard's assignment to `t`.
Consequently:

> **Theorem (the conjecture).** For every System T term `t : (ι⇒ι)⇒ι`,
> `h(dialogue-tree t) < ε₀`.
>
> *Established by:* Part I (rigorous reduction, new) `+` the standard
> ordinal analysis of T supplying (†) (Howard 1970; Schwichtenberg, Weiermann
> for the matching subrecursive hierarchies). Part II re-proves the
> first-order case self-containedly.

The supremum is exactly `ε₀`: the heights are cofinal in `ε₀` (the
query-nesting analogues of the fast-growing/Hardy functions realise every
tower `ω↑↑n`), while each individual term is strictly below it — the
finite-type-level/finite-degree phenomenon of III.2.

---

## Status — honest summary

* **Proved and self-contained:** Part I (reduction; the dialogue-specific
  content) and Part II (first-order/primitive-recursive fragment), plus
  L1–L3 (machine-checked in `DialogueTreeHeight.*`).
* **Identified and ground-verified:** the invariant `𝒫` and its ground
  closure (Lemma P).
* **Not finished from scratch:** obligation (†) — that `𝒫`'s invariant
  propagates through higher-type iteration. This is the genuine
  proof-theoretic core and coincides with the standard ordinal analysis of
  T; modulo that cited result the conjecture is proved, and I have not
  produced an independent, checked proof of (†).

So: the conjecture is **answered — it is true** — with the new
dialogue-theoretic half proved outright and the higher-type half reduced
to, and consistent with, the classical ε₀ analysis of Gödel's T. A fully
self-contained proof requires discharging (†), which is a substantial
proof-theory development in its own right.

---

## Part IV. The run at (†): why the strategy above fails, and what is actually needed

I attempted to discharge (†). It does not go through — and the reason is
not a missing lemma but a defect in the *invariant being propagated*. The
height-only majorant of Part I is too lossy: it over-estimates dialogue
heights all the way to `ε₀`. Here is the precise diagnosis.

### IV.1 The over-estimation, exactly

`iter' f x n = Kleisli-extension (iter f x) n` grafts the tree `fᵏ x` at
each leaf `η k` of the count `n`. **The iteration count at a leaf is that
leaf's value `k`**, and crucially `h(η k) = 0` for *every* `k`. So the
height-bound `ν = h(n)` carries **no information about the counts**: a
count `n = η m` (the numeral `m`, height `0`) and the count `n = η 0` are
indistinguishable to the majorant, yet they trigger `f^m` and `f^0`.

Forced by this, the iteration majorant takes the supremum over *all*
possible counts:
```
Φ_σ(φ)(a)(0) = φ^{(ω)}(a) = sup_{k<ω} φ^k(a).
```
That is: **"iterate `g` exactly `m` times" (a numeral `m`) is majorized by
"iterate `g` `ω` times".** At ground this is a mild over-shoot
(`ω` for a finite height). But it **compounds through higher types**:

> *Witness.* In the majorant calculus put `Add = Φ_ι(id)` (so
> `Add(a)(ν)=a+ν`), `double = λa. Add a a` (`a·2`),
> `W = Φ_ι(double)(–)(0)` (so `W(a)=a·ω`), and the functional
> `Ψ = λg. Φ_ι(g)(–)(0)` (so `Ψ(g) = g^{(ω)}`; note `Ψ(·γ) = ·γ^{ω}`).
> Then
> ```
> Φ_{ι⇒ι}(Ψ)(W)(0) (1) = ( sup_k Ψ^k(W) )(1) = ( sup_k ( ·(ω↑↑k) ) )(1) = 1·ε₀ = ε₀.
> ```
> Every ingredient here is `μ(s)` for an honest closed System T term `s`
> (these are just the recursor majorants composed by `K, S`); the term it
> majorizes is "iterate `Ψ` a *fixed numeral* number of times", whose true
> dialogue height is **finite**. So `μ(s) = ε₀` while `h(B⟦s⟧)` is finite.

Hence **`μ(s) < ε₀` is false in general**, and the "Reduction Theorem" of
Part I, though a correct inequality `h ≤ μ`, does **not** reduce the
*strict* conjecture to anything provable. The invariant `𝒫` of Part III
is moot: it is an invariant for the wrong quantity.

(What survives untouched: L1–L3; the inequality `h ≤ μ`; and Part II,
because in the first-order fragment the only counts that matter combine
with `▷ν` to give exact binary addition — e.g. `μ(Add)=a+ν` — and the
`ω`-overshoot stays below `ω^{ω}`, harmless there.)

### IV.2 What the correct majorant must track

The lesson is that **height alone is not a congruence for iteration**: the
height of `iter' f x n` depends on the *values* (leaf labels) of `n`, not
just its height. A faithful majorant of a ground object `x : B ℕ` must
bound *both*

1. its **height** `h(x)` (an ordinal), and
2. its **magnitude** — the leaf values / the size of `dialogue(x) α` as a
   function of a bound on the oracle `α`.

These interact in exactly the way Howard's *strong majorizability for the
continuous functionals* is designed for: a ground object is majorized
relative to a bound on the oracle, function objects are majorized
hereditarily, and the recursor is handled by simultaneously controlling
magnitude and an ordinal height. Only with the magnitude component can
`iter' f x n` be bounded by "`f` iterated (value of `n`) times", recovering
the strict `< ε₀` bound for each fixed term.

Concretely, the right statement to prove is something like: for a closed
`t : (ι⇒ι)⇒ι` and a modulus/oracle bound, the **pruned** dialogue tree (to
the Cantor cube `C = D ℕ 𝟚`, where values are bounded and branching is
finite) has a Howard ordinal `< ε₀`, and the full Baire height is the sup
of these over the bound — each `< ε₀`. This is the genuine ordinal
analysis of the dialogue/bar-recursion interpretation, and it is what
remains to be done.

### IV.3 Honest conclusion of the run

* The conjecture is still, to the best of my knowledge, **true** (it is the
  expected ε₀ analysis), but I have **not proved it**, and — importantly —
  the approach of Parts I–III **cannot** prove it as stated, because its
  central object (`μ`, the height-only majorant) genuinely reaches `ε₀`.
* The salvageable, rigorous results are: **L1–L3** (formalised), the
  inequality `h ≤ μ`, and **Part II** (the first-order/primitive-recursive
  fragment is `< ε₀`, self-contained).
* The correct path forward is a **two-component (magnitude + height)
  majorizability**, i.e. Howard's analysis adapted to dialogue trees, very
  plausibly first for the uniformly-continuous (pruned, Cantor) version
  where magnitudes are bounded, then taking suprema for the Baire version.
  I did not complete this.

I am flagging this rather than dressing the earlier sketch up as a proof:
the earlier "Part I is a complete reduction" was correct only as a
non-strict bound, and the witness in IV.1 shows why that is not enough.
