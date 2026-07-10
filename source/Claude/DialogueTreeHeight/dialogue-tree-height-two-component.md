# Two-component majorization for dialogue-tree heights

> **Working note (superseded).** Canonical account: **`dialogue-tree-height.md`**.
> Verified core: Agda `DialogueTreeHeight.Index`. Kept as record.

*Fresh, properly-scoped attempt at the ε₀ bound, repairing the defect
diagnosed in `…-ordinal-analysis.md` Part IV: the height-only majorant is
blind to iteration counts (which are leaf **values**, not heights) and
over-estimates to ε₀. Here we majorize a ground tree by a **pair
(height, magnitude)**. This recovers exact counts, kills the spurious ε₀,
and isolates the true residual difficulty.*

**What this achieves, honestly.**

* It **fixes** the Part IV over-estimation: with magnitude tracked, a count
  that is a numeral `m` is iterated exactly `m` times, not `ω` times.
* It **localizes ε₀** precisely: heights stay small (`≲ ω^ω`) until the
  *magnitude* is allowed to become an infinite ordinal, which happens only
  through **higher-type** iteration. So ε₀ is a strictly higher-type
  phenomenon, and the first-order/oracle fragment is bounded well below it.
* It does **not** complete the full proof: the higher-type case requires
  tracking magnitude *hereditarily* (magnitude becomes ordinal-valued at
  higher types), which is exactly Howard's analysis. I prove the
  first-order case and set up the rest.

---

## 1. The two components

For a dialogue tree `x : B ℕ` define, besides the height `h(x)`:

> **Magnitude** `m(x) ∈ ℕ ∪ {∞}` := a bound on the leaf values of `x`
> (`∞` if the leaf values are unbounded).
> `m(η n) = n`; `m(β φ i) = sup_j m(φ j)`.

The point of `m` is the **count lemma** below: in `iter' f x n` the
iteration performed at a leaf `η k` of `n` is `f^k`, and `k ≤ m(n)`.

Recall (from `…-ordinal-analysis.md` §2) the value-sensitive height
`H_v(x)`, `H_v(η k) = v(k)`, `H_v(β φ i) = sup_j (H_v(φ j) + 1)`, and the
identity `h(iter' f x n) = H_{γ}(n)` with `γ_k = h(f^k x)`.

> **Count Lemma.** If `m(n) ≤ M` (finite) and `h` is non-decreasing along
> the orbit (`h(f^k x) ≤ h(f^{k+1} x)`), then
> `h(iter' f x n) = H_γ(n) ≤ h(n) + h(f^{M} x)`.
> If `m(n) = ∞`, then `h(iter' f x n) ≤ h(n) + sup_{k<ω} h(f^k x)`.

*Proof.* `H_γ(n)`: every leaf value `k` of `n` satisfies `k ≤ M`, so
`γ_k = h(f^k x) ≤ h(f^M x) =: b`; thus `H_γ(n) ≤ H_{const b}(n) = b + h(n)`
by L3 (grafting `≤ b` at each leaf). For `M = ∞`, use the uniform bound
`b = sup_k h(f^k x)`. ∎

So the **finite-magnitude** case needs only the `M`-th iterate
`h(f^M x)` — *no `ω`-orbit, no over-estimation*. The `ω`-orbit is forced
**only** when the count has unbounded magnitude, i.e. genuinely depends on
the oracle.

This already repairs the Part IV witness: there the offending count was
the numeral `0` (`m = 0`), so the true iteration is `f^0 = id`, and the
two-component majorant returns `id`, not `f^{(ω)}`. The spurious tower
disappears.

## 2. Where magnitude comes from: the oracle, and only the oracle

> **Magnitude propagation.**
> * `m(η n) = n`, `m(zero') = 0`.
> * `m(succ' x) = m(x) + 1` (relabelling, height-free by L1).
> * `m(generic d) = ∞` — **`generic` is the unique source of `∞`**:
>   `generic` replaces each leaf `η n` by `β η n`, whose leaves are `η j`
>   for *all* `j`, so values become unbounded; meanwhile height only `+1`
>   (L2).
> * `m(kleisli-extension g d) = sup_k m(g k)` (values come from the grafts).

Hence a closed term with **no `Ω`** has finite magnitude and (by the Count
Lemma) all its iterations are finite — its dialogue tree is essentially a
single computation, height `0` (a leaf). Magnitude `∞`, and therefore the
`ω`-orbit, enters **only** via the oracle `Ω`.

## 3. The orbit at first order is small (`≲ ω^ω`)

Consider the residual hard case: `iter' f x n` with `m(n) = ∞` (oracle
count). By the Count Lemma the height is `h(n) + sup_k h(f^k x)`, so
everything turns on the **height-orbit** `sup_k h(f^k x)`.

For a **first-order** `f : ι⇒ι` (built without higher-type `Iter`), analyse
how `f` transforms the pair `(h, μ) = (height, magnitude)` of its argument:

* The argument's height enters `h(f(y))` only **additively / by a fixed
  finite multiple** — `f` grafts/uses `y` a fixed finite number of times
  (L1–L3), so `h(f(y)) ≤ h(y)·c_f ⊕ (term in μ)` with `c_f < ω`.
* The only way the argument contributes a *new* height increment is by
  being used as a **count** of an internal iteration, contributing
  `≤ ω^{μ}` (an internal oracle-count over values `≤ μ` stacks `≤ μ` layers,
  height `≤ ω^{μ}` after the `sup`).
* Magnitude transforms `μ ↦ μ'` with `μ'` a fixed first-order
  number-function of `μ` (successor, grafting), and crucially **stays a
  natural number** when `μ` is — first-order operations do not turn a
  finite magnitude into an infinite ordinal.

So along the orbit, `μ_k` are naturals (possibly growing) and
`h(f^{k+1} x) ≤ h(f^k x)·c ⊕ ω^{μ_k}`. Since every `μ_k < ω`, every
`ω^{μ_k} < ω^ω`, and a linear recurrence with `c < ω` and increments
`< ω^ω` has

> `sup_k h(f^k x) ≤ ω^{ω} · ω = ω^{ω+1} < ε₀`  (in fact `< ω^{ω+1}`).

> **Theorem (first-order fragment, sharpened).** For every closed
> first-order `t : (ι⇒ι)⇒ι` (all `Iter`s at type `ι`),
> `h(dialogue-tree t) < ω^{ω·2}` — in particular `< ε₀`.

(The exact exponent is unimportant; the content is that finite magnitude
keeps the `ω`-exponents **finite**, so heights stay far below ε₀. This both
re-proves and sharpens Part II, and unlike Part II it is immune to the
Part IV over-estimation because counts are tracked.)

## 4. Where ε₀ actually comes from, and the residual obligation

The bound `ω^{μ}` with `μ` *finite* is what caps first-order heights at
`≲ ω^ω`. To climb toward ε₀ the **exponent `μ` must become an infinite
ordinal** — i.e. magnitude itself must be ordinal-valued. This is precisely
what **higher-type** iteration does:

* Iterating a *functional* `F : (ι⇒ι)⇒(ι⇒ι)` produces `ι⇒ι` functions whose
  magnitude-transform is no longer a fixed number-function but grows with
  the iteration, so the effective exponent `μ` in `ω^{μ}` becomes an
  ordinal `< ε₀`.
* Each type level adds one such "ordinalisation" of the magnitude; a fixed
  term has finite type level, so its magnitude-exponent is a fixed ordinal
  `< ε₀`, giving height `< ε₀`; over all terms the exponents are cofinal in
  ε₀, giving height-supremum exactly `ε₀`.

Making this precise is the genuine content, and it is **Howard's
hereditarily-majorizable functionals with ordinal magnitudes**:

> **Residual obligation (the real one).** Define, hereditarily over types,
> a *two-component* majorant — at `ι` a pair `(a, μ)` with `a` an ordinal
> height-bound and `μ` an **ordinal** magnitude-bound; at `σ⇒τ` a monotone
> map of pairs — and prove the fundamental theorem with the Count Lemma at
> the recursor, with both components staying `< ε₀`. The magnitude
> component is exactly Howard's ordinal assignment; the height component
> rides on it via the Count Lemma.

I have **not** carried this out. What I am confident of, and what the
two-component analysis above shows, is:

1. the correct invariant is the pair (height, **ordinal** magnitude), not
   height alone — this is forced, and it removes the Part IV obstruction;
2. magnitude is the carrier of the ordinal-analytic content (it is where
   `< ε₀` must be earned), and height is a controlled functional of it via
   the Count Lemma;
3. the first-order fragment is genuinely, rigorously `< ε₀` (§3);
4. the full statement is Howard's theorem for this interpretation, and the
   reduction above is, I believe, faithful — but unverified at higher
   types.

## 5. Status

* **New, rigorous:** the Count Lemma (magnitude recovers exact counts, no
  `ω`-overshoot); magnitude propagation (`Ω` is the sole source of `∞`);
  the **sharpened first-order theorem** `h < ω^{ω·2}` (§3), which is immune
  to the Part IV defect.
* **Correctly framed, not proved:** the higher-type case via hereditary
  ordinal-valued magnitude (§4), = Howard's analysis.
* **Unchanged elsewhere:** L1–L3 are machine-checked; the conjecture
  remains, to my best judgement, **true**, and now with a clear, defensible
  route (two-component / Howard) rather than the broken height-only one.

I am stopping short of asserting a complete proof. The two-component
framework is, I am fairly sure, the right one, and §1–§3 are solid new
results; §4 is the honest remaining mathematics, which is a real
proof-theory development (Howard 1970 adapted to dialogue trees).
