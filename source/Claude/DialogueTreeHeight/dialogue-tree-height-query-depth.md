# The query-nesting-depth analysis: the right invariant is an operator

> **Working note (superseded).** Canonical account: **`dialogue-tree-height.md`**.
> Verified core: Agda `DialogueTreeHeight.Index`. The operator `H` developed
> here is the one machine-checked in `DialogueTreeHeight.Operator`. Kept as record.

*Strategy document for the residual lemma R3, after the discovery
(`…-howard-build.md` revisited) that height is **not** controlled by
magnitude rank. Here I identify the correct invariant — a height-transform
**operator** `𝓗_x` — prove the structural identities it satisfies
(**[PROVABLE]**, formalisable), and reduce the conjecture to a single
boundedness statement about these operators (**[CONJECTURAL]**, = the
genuine ordinal analysis). This is a map of the proof, not the proof.*

Tags: **[PROVABLE]** = I have a proof (induction; formalisable);
**[CONJECTURAL]** = the open ordinal-analytic core.

---

## 0. Why a scalar invariant cannot work

The counterexample that sank the two-component story:
`x = iter' generic base (generic (η 0))` has height `ω` but value-magnitude
of rank `0`. Height is query-nesting depth; it is independent of value
size. So no scalar magnitude controls it. The fix is to track, for each
ground object, **how it transforms an ordinal valuation of its leaves** —
because that is exactly what iteration reads.

## 1. The height-transform operator

For `v : ℕ → Ord` and `x : B ℕ` define the **value-sensitive height**
```
𝓗_x(v) := H_v(x),    H_v(η k) = v k,    H_v(β φ i) = sup_j (H_v(φ j) + 1).
```
`𝓗_x : (ℕ→Ord) → Ord` is monotone. Two shadows:

* ordinary height `h(x) = 𝓗_x(0̄)` (the constant-`0` valuation) — **[PROVABLE]**
  (induction: both sides satisfy the same recursion);
* value-distribution order type `τ(x) := 𝓗_x(id)` (leaf value `k` weighted
  by the ordinal `k`).

Examples (all by direct computation, **[PROVABLE]**):
`𝓗_{η m}(v) = v m` (a leaf reads the **exact** count `m`);
`𝓗_{generic(η0)}(v) = sup_j (v j + 1)` (the oracle reads the **sup** over
all counts). This is the clean unification the scalar magnitude missed: a
leaf gives an exact count, the oracle gives an `ω`-supremum.

## 2. The composition law and the recursor identity — [PROVABLE]

> **Composition law.** For `g : ℕ → B ℕ`, `d : B ℕ`, `v : ℕ → Ord`,
> ```
> 𝓗_{kleisli-extension g d}(v) = 𝓗_d ( k ↦ 𝓗_{g k}(v) ).
> ```

*Proof.* Induction on `d`. Leaf `η k`: LHS `= 𝓗_{g k}(v)`, RHS `=
(k' ↦ 𝓗_{g k'}(v))(k) = 𝓗_{g k}(v)`. Node `β φ i`: both sides are
`sup_j ( … + 1)` and agree by the IH on `φ j`, since
`kleisli-extension g (β φ i) = β (λj → kleisli-extension g (φ j)) i`. ∎

Since `iter' f x n = kleisli-extension (iter f x) n` and
`(iter f x) k = fᵏ x`, taking `v = 0̄` and `h = 𝓗_-(0̄)` gives:

> **Recursor identity.** `h(iter' f x n) = 𝓗_n ( k ↦ h(fᵏ x) )`. **[PROVABLE]**

This is the exact statement the whole analysis turns on: **the count tree
`n` acts on the orbit of heights `k ↦ h(fᵏ x)` through its operator `𝓗_n`.**
A leaf count `η m` selects `h(f^m x)` (exact `m`-fold); a generic count
takes the supremum (forced `ω`-orbit). Both the Count Lemma and the
spurious-ε₀ pathology are special cases, now unified and exact.

(Both the composition law and the recursor identity are formalisable on top
of `DialogueTreeHeight.Constructive`/`…Count`, by adding `H_v` and one
induction. I have not yet formalised them, per "prove first".)

## 3. Operator algebra of the combinators — [PROVABLE]

Each builder acts on `𝓗`:

* `𝓗_{η n}(v) = v n`.
* `𝓗_{succ' x} = 𝓗_x` — relabelling is height-free (L1); `succ'` does not
  change the *shape*, only leaf values, but `𝓗` already abstracts leaves
  by `v`, so... **caveat:** `succ'` shifts which `v`-index each leaf reads
  (`η n ↦ η (n+1)`), so precisely `𝓗_{succ' x}(v) = 𝓗_x(v ∘ succ)`. **[PROVABLE]**
* `𝓗_{generic x}(v) = 𝓗_x ( k ↦ sup_j (v j + 1) )` — by the composition law
  with `g = β η`, since `𝓗_{β η k}(v) = sup_j(v j + 1)`, independent of `k`.
  **[PROVABLE]** So `generic` **collapses** the valuation to its capped
  supremum `S := sup_j(v j + 1)` and then runs `x` on the constant `S̄`;
  hence `𝓗_{generic x}(v) = S + h(x)` (grafting the constant `S`). This is
  the operator form of "the oracle resets to the sup, height `+ h(x)`".

So `generic` is the **only** builder that introduces a supremum over all
counts; everything else either selects exact indices (`η`), reindexes
(`succ'`), or grafts (composition law). This re-confirms, now at the
operator level: **unbounded query nesting enters solely through `Ω`.**

## 4. The reduction — [PROVABLE reduction] to one [CONJECTURAL] bound

Define the hereditary majorant with **operator-valued** ground component:
at `ι`, majorize `x` by (a bound on) the monotone operator `𝓗_x`; at
`σ⇒τ`, by monotone maps as before. The fundamental theorem then runs with
the recursor handled by §2's identity. Everything reduces to controlling
the operators that arise, i.e. to:

> **Lemma R3′ (operator boundedness).** **[CONJECTURAL]**
> For every closed `t : (ι⇒ι)⇒ι`, the operator `𝓗_{dialogue-tree t}`
> evaluated at `0̄` is `< ε₀`; more strongly, the operators arising in all
> orbits stay within a class closed under §3's algebra and §2's
> composition, with `0̄`-values cofinal in but below `ε₀`.

This is R3 in its correct form. It is *not* reducible to Howard's value
analysis (§0). It is the ordinal analysis of the **operators**, i.e. of
query-nesting depth.

## 5. Heuristic for why R3′ should hold (not a proof)

`𝓗_x(v)` is built from `v` using **only** `sup` and `+1` (and the fixed
tree shape). Crucially there is **no exponentiation primitive** on `v`:

* a single `generic` turns a valuation into `v ↦ sup_j(v j + 1)` — it can
  manufacture a *limit*, but only an `ω`-sup of the existing values `+1`;
* grafting (composition law) substitutes operators into each other —
  additive/`sup` in effect, never `v ↦ ω^{v}`.

So one "level" can multiply the relevant ordinal by `ω` (a `sup` of `+1`s)
but cannot exponentiate it. A tower — and hence `ε₀` in the limit — can
only be assembled by **nesting** these levels, and the nesting depth
available to a fixed term is bounded by its **type level** (each
higher-type iteration permits one more level of operator-into-operator
substitution). Finite type level ⇒ finite tower ⇒ `< ε₀`; cofinally over
all terms ⇒ supremum exactly `ε₀`.

Making "type level bounds operator-nesting depth, and each level multiplies
by `ω`" precise is the content of R3′. The operator framework makes the
*shape* of the argument clear — it is a structural induction on types with
the composition law (§2) at the recursor — but I have **not** verified that
the operator class is genuinely closed with the `ε₀` bound, and the history
of this thread says I should not assert closure I have not checked.

## 6. Status

* **[PROVABLE / formalisable]:** the operator `𝓗_x`; `h = 𝓗_-(0̄)`; the
  **composition law**; the **recursor identity** `h(iter' f x n) =
  𝓗_n(k ↦ h(fᵏ x))`; the combinator operator algebra (§3), including that
  `Ω` is the unique source of suprema.
* **[CONJECTURAL]:** R3′ — operator boundedness `< ε₀`. This is the genuine
  ordinal analysis of query-nesting depth, with §5 a heuristic for its
  truth, not a proof.

**Net.** This replaces the broken scalar-magnitude picture with the correct
**operator-valued** invariant `𝓗_x`, and pins the entire remaining
difficulty to the single, sharply-stated, *correctly-formulated* Lemma R3′,
together with the provable composition law that is its engine. The
conjecture holds iff R3′ does. I believe R3′ is true; I have not proved it,
and I am labelling it as such.

---

## 7. Direct attempt at R3′ (the type-level induction) — findings

I attacked R3′ head-on via the operator framework. Three genuine outcomes,
including a correction of an error I nearly made.

### 7.1 A tempting wrong characterisation (corrected)

It is tempting to think `𝓗_x(v) = sup_{leaves ℓ} ( depth(ℓ) + v(value(ℓ)) )`
with `depth(ℓ)` finite, which would force `h(x)=𝓗_x(0̄) ≤ ω` and make the
whole conjecture trivial. **This is false.** The recursor `H_v(β φ i) =
sup_j (H_v(φ j) + 1)` does **not** flatten, because `sup_j (β_j + 1) ≠
(sup_j β_j) + 1` in general (`β_j = j`: `ω` vs `ω+1`). The `+1`s are
interleaved with the suprema, so `𝓗_x` is the genuine ℕ-branching **tree
rank** — a real countable ordinal, reaching `ε₀`. (Worth stating to forbid
this dead end.)

### 7.2 Scalarisation through `generic`, and that the `ω`-orbit is *real*

Let `φ_x(β) := 𝓗_x(λ_. β)` (constant valuation; note `φ_x(0)=h(x)`) and
`σ(v) := sup_j (v j + 1)`. By §3,
```
𝓗_{generic d}(v) = φ_d(σ(v)),
```
so **after a `generic`, the operator depends on `v` only through the single
ordinal `σ(v) = sup of the values`.** Hence for a top-level oracle count,
the recursor identity gives, *exactly*,
```
h(iter' f x (generic …)) = φ_{…}( sup_k h(fᵏ x) ).
```
So the `ω`-orbit `sup_k h(fᵏ x)` is **not** an over-estimation here — for an
oracle-driven count it is the true value (the oracle really ranges over all
counts). The Part IV over-estimation was *only* for **leaf** counts (exact
`m`-fold), which the Count Lemma already handles. Conclusion: **R3′ at
`v=0̄` genuinely requires `sup_k h(fᵏ x) < ε₀`** — there is no slack to
exploit; it is a real demand.

### 7.3 The obstruction is genuine: no scalar recurrence

Write `T_f` for `f`'s operator transform, `𝓗_{f(y)} = T_f(𝓗_y)`. Then the
orbit is `𝓗_{fᵏ x} = T_f^k(𝓗_x)` and the requirement is
`sup_k T_f^k(𝓗_x)(0̄) < ε₀`. The difficulty, made precise: **`T_f(Ψ)(0̄)`
depends on `Ψ` globally** (on `Ψ` at many arguments, via the values that
`f` queries/iterates), not just on `Ψ(0̄)`. So there is no scalar recurrence
`a_{k+1} = g(a_k)` to solve; one must control the whole operator along the
orbit. That is exactly a hereditary ordinal assignment to the operators —
i.e. Howard's analysis transported to `𝓗`. The operator language makes the
*shape* crisp (structural induction on types, composition law at the
recursor) but does **not** remove the core work, and I did not find a way to
collapse it to something I can verify.

### 7.4 Honest bottom line on R3′

R3′ is the ordinal analysis of Gödel's T in operator form. Across repeated
direct attempts I have: identified the correct invariant (`𝓗_x`), proved
and **formalised** its algebra (`DialogueTreeHeight.Operator`), shown the
`ω`-orbit demand is real (§7.2), and isolated the precise obstruction
(§7.3). I have **not** proved R3′ and, given the track record in this
development, I will not assert a closure I cannot check. Further refinement
of the reduction is possible, but it will keep bottoming out at the same
hereditary operator bound, which is a genuine proof-theory theorem rather
than something a few more steps will dislodge.

### 7.5 A definite negative result: one component does not suffice

It is natural to hope to track just the scalar **height-envelope**
`φ_x(β) = 𝓗_x(λ_. β)` hereditarily (one ordinal function per object) and
close the induction with it. **This provably fails**, and the failure is
worth stating precisely because it shows *what any correct proof must do*.

> **Proposition.** A hereditary majorant whose ground component is `φ_x`
> alone (the constant-valuation envelope) cannot prove `h < ε₀`: it assigns
> some closed terms the value `ε₀`.

*Proof.* `φ_x` over-estimates `𝓗_x` on non-constant valuations: by
monotonicity `𝓗_x(v) ≤ φ_x(sup_m v m)`, and this is **strict** exactly when
`x` reads its leaves selectively — e.g. `𝓗_{η m}(v) = v m` but
`φ_{η m}(sup v) = sup v`. In the recursor identity
`h(iter' f x n) = 𝓗_n(k ↦ h(fᵏ x))`, a **leaf** count `n = η m` selects the
exact iterate `h(f^m x)`, whereas the envelope replaces it by
`φ_{η m}(sup_k h(fᵏ x)) = sup_k h(fᵏ x)` — the full `ω`-orbit. That is the
Part IV over-estimation, and §IV.1's witness (a fixed-numeral count
compounded through `ι⇒ι` iteration) then drives the envelope value to `ε₀`
while the true height is finite. ∎

So count-exactness for oracle-free (bounded-magnitude) counts is **not**
optional: any correct invariant must carry, hereditarily, the magnitude
information (the `values-≤` data of `DialogueTreeHeight.Count`) *alongside*
the height-envelope. This is precisely Howard's two-component hereditary
assignment, and it is now established here as **necessary**, not merely
sufficient: neither component alone works (height-only over-estimates via
the count; magnitude-only misses the height, §0). The proof of R3′ must run
the two together, which is the genuine ordinal-analytic development.
