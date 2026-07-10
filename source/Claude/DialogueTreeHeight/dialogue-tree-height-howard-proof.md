# A scoped two-component proof (in progress)

> **Attribution correction (read first).** This file is named "Howard-style"
> and at points treated the height bound as Howard's. **That is wrong.**
> Howard (1970) bounds *value/reduction* complexity of System T terms and
> contains no dialogue trees; dialogue height is independent of value
> magnitude (§0), so Howard does not bound it. Howard is relevant only as a
> *method* (hereditary ordinal assignment) and only legitimately for the
> *magnitude* side. The problem belongs to the Gentzen–Tait–Schütte
> ordinal-analysis tradition applied to Escardó's dialogue strategy trees;
> the conjecture is Escardó's and open. See
> `dialogue-tree-height-correct-framing.md` for the corrected record. The
> "two-component" mathematics below stands; the Howard *naming/attribution*
> does not.

## (original title: "A scoped Howard-style two-component proof")

*The living proof attempt. Goal: `h(dialogue-tree t) < ε₀`. Both components
(magnitude + height) are tracked **together**, since §7.5 of
`…-query-depth.md` shows neither alone suffices. Status tags:* **[P]**
proved here; **[P✓]** proved and machine-checked already; **[P|H]** proved
modulo Howard's value theorem (a published result); **[OPEN]** the genuine
remaining step.

Standard ε₀ facts used freely (CNF, closure under `⊕,⊗,ω^·`, fundamental
sequences). `F_β` (`β<ε₀`) is the fast-growing hierarchy; Howard's theorem:
every System T number-function is `≼ F_β` for some `β<ε₀`.

---

## 1. The combined majorant — [DEFINED]

Oracle bounds: `b : ℕ`; `α ≤ b` means `∀i, α i ≤ b`. Write `dlg x α =
dialogue x α`.

> `Maj_ι = Ord × (ℕ→ℕ_mono)`, `Maj_{σ⇒τ} =` monotone `Maj_σ → Maj_τ`.

> `x ◁_ι (a, V)` :⟺ `h(x) ≤ a` (height) **and** `∀b ∀α≤b, dlg x α ≤ V b`
> (magnitude). `F ◁_{σ⇒τ} φ` :⟺ `∀ x p, x ◁ p → F x ◁ φ p`.

Projections `π_h(a,V)=a`, `π_m(a,V)=V`. The point: `π_m` is read by the
recursor's *count*; `π_h` is the tree rank; they are independent (a tree can
have large rank with bounded values, §0) but couple at the recursor.

## 2. Magnitude is Howard's setting — [P] structural, [P|H] for the bound

The `π_m`-projection of `◁` is exactly Howard strong majorizability of the
number-function `α ↦ dlg x α`. The combinators:

* `dlg (η 0) α = 0`        ⟹ `zero' ◁ (0, λb.0)`. **[P]**
* `dlg (succ' x) α = dlg x α + 1` (naturality) ⟹ magnitude `V ↦ (b↦Vb+1)`. **[P]**
* `dlg (generic x) α = α(dlg x α) ≤ b` for `α≤b` (generic diagram) ⟹
  magnitude `V ↦ (λb.b)`, **independent of `V`** (the oracle resets). **[P]**
* `K, S`: the standard majorants `λV W.V`, `λΦΨV. ΦV(ΨV)`. **[P]**
* **Recursor (magnitude).** `iter' f x n` has count `dlg n α ≤ W b`
  (`n ◁ (ν,W)`), so its value-function is `f`'s magnitude-functional `Φ`
  iterated `W b` times from `V_x`: `V'(b) = Φ^{(W b)}(V_x)(b)`. **[P]**
  structurally (Count Lemma R1); and `V' ≼ F_β`, `β<ε₀`, by **Howard's
  theorem [P|H]** — values are just System T outputs.

So the magnitude component is finished modulo the cited value theorem. The
height component is the new mathematics.

## 3. Height combinators — [P] / [P✓]

Using L1, L2 (machine-checked) and the operator `H` of §`DialogueTreeHeight.Operator`:

* `zero' ◁` height `0`. **[P✓]** (`h(η0)=0`).
* `succ' ◁` height `a ↦ a` (L1, relabelling height-free). **[P✓]**
* `generic ◁` height `a ↦ a+1` (L2). **[P✓]**
* `K, S` structural. **[P]**

All clean; the difficulty is entirely the recursor's height component.

## 4. The recursor's height — the heart

Setup: `f ◁ φ`, `x ◁ (a₀,V₀)`, `n ◁ (ν,W)`. Orbit `(a_k,V_k) := φ^k(a₀,V₀)`,
so `f^k x ◁ (a_k,V_k)` **[P]** (induction). By the **recursor identity**
(machine-checked, `height-iter'`):
```
h(iter' f x n) = 𝓗_n( k ↦ h(f^k x) ) ≤ 𝓗_n( k ↦ a_k ).
```
Two regimes, split by the count's magnitude `W`:

### 4a. Bounded count `W ≤ M < ω` — [P✓]
Then `n` has `values-≤ M` (machine-checked predicate), only `k ≤ M` occur,
and the **Count Lemma** (`height-kleisli-extension-≤`, formalised) gives
```
h(iter' f x n) ≤ a_M + ν     (exact M-fold; no over-estimation).
```
This case is *done and verified.* The Part IV pathology lived here and is
now provably absent.

### 4b. Unbounded count (oracle-driven `W`) — reduces to one orbit bound
The leaves realise all values, and (scalarisation, §7.2)
`𝓗_n(k ↦ a_k) ≤ ν + sup_k a_k`. So the **entire** remaining difficulty is:

> **Orbit lemma (OL).** `sup_k a_k < ε₀`, where `(a_k,V_k) = φ^k(a₀,V₀)` is
> the combined orbit of a System-T-arising majorant `φ`.

Everything else is proved. OL is the Howard recursor lemma for the *height*
component, and it is genuinely coupled to the magnitude `V_k` (next).

## 5. The orbit lemma OL — first order [P], higher order [OPEN]

The height recurrence along the orbit is
```
a_{k+1} ≤ G_f(a_k, V_k),
```
where `G_f` is `f`'s height-transform: the input height enters **additively
/ by a fixed finite multiple** (grafting, L1–L3), and the input *magnitude*
`V_k` enters through any internal iteration of `f` whose count `f` reads.

### 5a. First order — [P]
If `f` is first order, `G_f(a,V) ≤ a·c ⊕ d(V)` with `c<ω` and `d(V)` a term
in `ω^{(finite)}` (an internal oracle-count over bounded-rank values stacks
finitely many `ω`-powers, §`…-two-component.md` §3). Since `V_k ≼ F_β` with
`β` **finite** at first order, `d(V_k) < ω^ω`, and the linear recurrence
gives `sup_k a_k ≤ ω^{ω·2} < ε₀`. ∎ This reproves the first-order theorem
inside the combined framework — now with the magnitude component making the
`d(V_k)` bound rigorous rather than schematic.

### 5b. Higher order — [OPEN], and *why* it is the real theorem
At higher type, `G_f` is **not** a closed function of `(a, V)`: the internal
iteration `f` performs may itself have an oracle-driven count, so
`G_f(a_k,V_k)` is itself defined by an orbit-sup of the same kind (the §0
phenomenon: a height contribution from an unbounded internal count is
rank-independent and must be computed by *its* orbit lemma). Thus OL is
**self-referential through the type structure**: bounding `sup_k a_k`
requires already bounding the inner orbits, one type level down.

The correct device is therefore a **well-founded ordinal assignment**
`ρ(φ) < ε₀` to majorant-functionals, with:
* `ρ` strictly decreasing along the structural recursion of `G_f` (so the
  self-reference is well-founded), and
* the orbit-sup at rank `ρ` bounded by the **fundamental-sequence limit**:
  `sup_k a_k ≤ a_0 ⊕ (period) · ω^{ρ(φ)}` (schematically), with
  `ρ(φ) < ε₀` because a fixed term has finite type level and each level
  raises `ρ` by a bounded ordinal.

This is exactly Howard's recursor lemma, transported from values to tree
rank. I have **not** constructed `ρ` and proved its two properties; that is
the remaining content, and it is a genuine proof-theory construction (a
well-founded ordinal assignment with a fundamental-sequence orbit bound),
not a calculation.

## 6. What "starting the proof" has established

| Piece | Status |
|---|---|
| Combined majorant `Maj_σ`, `◁` | **[DEFINED]** |
| Magnitude combinators + recursor (structure) | **[P]** |
| Magnitude bound `V ≼ F_{<ε₀}` | **[P|H]** (Howard) |
| Height combinators (zero, succ, generic, K, S) | **[P]/[P✓]** |
| Recursor identity `h(iter') = 𝓗_n(orbit)` | **[P✓]** |
| Recursor height, **bounded count** (4a) | **[P✓]** (Count Lemma) |
| Recursor height, unbounded ⟹ **OL** (4b) | **[P]** reduction |
| OL, **first order** (5a) | **[P]** (`< ω^{ω·2}`) |
| OL, **higher order** (5b) | **[OPEN]** = the `ρ`-assignment + fundamental-sequence bound |

**Net.** The proof is now a single, well-defined object with exactly one
open node: construct the well-founded ordinal assignment `ρ` on
majorant-functionals and prove the fundamental-sequence orbit bound at each
rank (5b). Everything feeding into it — the combined majorant, the
magnitude side (Howard), all height combinators, the recursor identity, the
bounded-count case, and the first-order orbit bound — is proved, much of it
machine-checked. This is the scoped Howard-style proof, started, with the
remaining work localised to one construction.

## 7. The immediate next target (concrete)

Construct `ρ : Maj-functionals → ε₀` with:
1. `ρ(combinator) = 0` for `zero', succ', generic, K, S`;
2. `ρ(φ ψ) ≤ ρ(φ) ⊕ ρ(ψ)` (application);
3. `ρ(μIter at type σ) = ρ_σ`, a fixed ordinal `< ε₀` with `ρ_σ` strictly
   above the ranks of `σ`'s components (one Grzegorczyk/Veblen step per type
   level);
4. **Orbit bound:** `sup_k π_h(φ^k p) ≤ π_h(p) ⊕ ω^{ρ(φ)}·ω` for `φ` of
   rank `ρ(φ)`, proved by the fundamental sequence of `ω^{ρ(φ)}`.

(3)+(4) are the Howard recursor lemma. Proving them — in particular that the
self-reference in 5b respects the `ρ`-ordering — is the next unit, and is
the right place to either grind the proof or, pragmatically, discharge (4)
by citing the fast-growing-hierarchy bound and verifying the height side
rides on it.

---

## 8. The linearity insight — a candidate completion of OL

*Constructing `ρ`, I hit on the structural fact that makes `(4)` true with
`ρ(φ)` linear data. I believe this **completes OL**, hence the conjecture.
It is freshly derived and **not yet formalised or independently checked**;
given this thread's history I present it for scrutiny, not as settled.
Operations `⊕,⊗` are natural (Hessenberg) sum/product; ε₀ is closed under
them and under `c ↦ c^{⊗ω} = sup_k c^{⊗k}`.*

### 8.1 The crux: height is not a value — [conceptual, solid]

A System T term computes **outputs** `dlg y α`; the height `h(y)` is the
rank of its **query tree** — how deeply queries nest — which is a meta-level
property the term has no access to. In particular **no term computes `h(y)`
as a value.** Therefore, in `iter' g base (count)`, the count is the
*value* `dlg(count) α`, a **magnitude** quantity, *never* the height. So:

> **The number of times a ground input `y` is grafted/iterated is always a
> magnitude (value) quantity, independent of `h(y)`.**

Consequently the height-transform is **linear in the input height**: `f`
can graft `y` "magnitude-many" times — a fixed ordinal `c < ε₀`,
oracle-`ω` or finite — but never "`h(y)`-many" times. This is why
super-linear growth (`h(y)²`, `ω^{h(y)}`) — the only thing that could reach
ε₀ under iteration — **cannot occur.**

### 8.2 The Linearity Lemma — [candidate proof]

> **Linearity Lemma.** For every System T term, the height of its
> fully-ground-applied dialogue value is bounded by a **linear form**
> ```
> h ≤ ( ⊕_i  h(y_i) ⊗ c_i )  ⊕  D,
> ```
> over the ground inputs `y_i`, with all coefficients `c_i < ε₀` and
> constant `D < ε₀` (depending on the magnitudes — by Howard `≼ F_{<ε₀}` —
> and on the other inputs, but **not** on the `h(y_i)`).

Hereditary form (for the induction): a *tame functional* sends tame
arguments — carrying `< ε₀` linear data — to tame results with `< ε₀`
linear data, the data combining under `⊕, ⊗, (·)^{⊗ω}`.

*Proof, by induction on the term.*

* `Zero, Succ, K, S, η`, application: linear forms compose under `⊕, ⊗`
  (grafting adds heights, L1–L3); coefficients combine, staying `< ε₀`.
  `S`'s diagonal duplicates a ground slot, multiplying its coefficient by a
  fixed finite amount — still `< ε₀`.
* `Ω = generic`: `h ↦ h+1`, a linear form with `c=1, D=1`.
* **Recursor `iter' f x n` (the crux).** Let `f` have, by IH, height-
  transform `h(f(y)) ≤ (h(y) ⊗ c) ⊕ D` (`c, D < ε₀`). Then
  `h(f^k x) ≤ (h(x) ⊗ c^{⊗k}) ⊕ D⊗(c^{⊗(k-1)} ⊕ ⋯ ⊕ 1)` (induction on `k`,
  `⊗` distributing over `⊕`). Now:
  * **bounded count** `n` (magnitude `≤ M`): by the Count Lemma (4a) only
    `k ≤ M` occur, and every finite iterate is `≤ sup_k h(f^k x)`; so
    `h(iter' f x n) ≤ ( h(x) ⊗ c^{⊗M} ) ⊕ D' ⊕ h(n)`.
  * **unbounded count** (4b): `h(iter' f x n) = sup_k h(f^k x) ⊕ h(n)
    ≤ ( h(x) ⊗ c^{⊗ω} ) ⊕ D'' ⊕ h(n)`,
    where `c^{⊗ω} = sup_k c^{⊗k} < ε₀` (closure) and `D'' = sup_k D⊗(⋯) =
    D ⊗ c^{⊗ω} < ε₀`.

  At **ground** type (`σ = ι`, `f : ι⇒ι`) the result is a **linear form** in
  `h(x)` (coefficient `c^{⊗M}` or `c^{⊗ω}`, both `< ε₀`) and `h(n)`
  (coefficient `1`), constant `< ε₀`. So at ground the recursor's only effect
  on a coefficient is `c ↦ c^{⊗ω}`. ∎(ground)

The self-reference flagged in §5b is resolved at ground: the additive
constant absorbs subterm orbit-sups `sup_k h(g^k base)`, each a *fixed*
`< ε₀` ordinal from the IH on the structurally smaller subterm `g`.

### 8.3 Higher type: `(·)^{⊗ω}` per level compounds to towers — corrected

I initially wanted "the recursor's only effect is `c ↦ c^{⊗ω}`" uniformly.
**That is false at function type**, and the correction is the real
mechanism. When `Iter` is at a *function* type `σ = ρ⇒…`, the iterated
functional `F`'s effect on its argument's **coefficient** is itself a
`(·)^{⊗ω}` (its body contains a recursor). Iterating `F` therefore
compounds:
```
size_{j+1} = size_j^{⊗ω}  ⟹  size_k = c^{⊗ω^k},  orbit sup = c^{⊗ω^ω},
```
and one further type level gives `c^{⊗ω^{ω^ω}}`, etc. So **each type level
contributes one `ω` to an exponent tower**:
```
coefficient at type level ℓ  ≤  c^{⊗ (ω↑↑ℓ)}  <  ε₀  for every finite ℓ,
```
while `sup_ℓ ω↑↑ℓ = ε₀`. This is exactly where ε₀ comes from, and why it is
the supremum but never attained: a fixed term has **finite type level**, so
a finite tower, so `< ε₀`; the family is cofinal in ε₀.

Linearity (§8.1) is what makes each level's operation `(·)^{⊗ω}` rather than
genuine exponentiation `c ↦ ω^{c}` — the latter would already reach ε₀ at
one level. So §8.1 caps the *per-level* growth; the *type-level* induction
caps the nesting. Together:

> **Reduction (candidate).** OL holds, with the bound
> `h(dialogue-tree t) < ω↑↑(ℓ(t) + s(t)) < ε₀`,
> where `ℓ(t)` is the type level and `s(t)` a size term — provided the
> coefficient bookkeeping of §8.3 is correct across the function-typed
> combinator cases.

### 8.4 Conclusion (candidate) and honest caveats

Applying the Linearity Lemma + §8.3 to `dialogue-tree t = B⟦t⟧ generic`
(closed ground, no free `y_i`) bounds its height by a constant
`< ω↑↑(finite) < ε₀`:

> **Theorem (candidate).** `h(dialogue-tree t) < ε₀` for every System T
> `t : (ι⇒ι)⇒ι`, with the explicit bound `< ω↑↑(finite)` per term.

**What must be checked before believing it:**

1. **The function-typed coefficient algebra (§8.3).** The claim "each type
   level adds one `ω` to the tower" rests on the precise rule for how a tame
   *functional*'s coefficient transforms its *argument*'s coefficient, and
   that iterating it does `(·)^{⊗ω}`. The ground case is clean; the
   function-type case is argued but not written out per combinator (`S` with
   function arguments, `Iter` at type `σ⇒τ`). **This is the one place a hidden
   super-linearity could still lurk** — though §8.1 (height is never a count)
   is a strong structural reason it cannot.
2. **Orbit/Count-Lemma interface (4a/4b):** monotonicity of the orbit and the
   `⊗`-over-`⊕` distributivity used — routine, unverified.
3. **Not formalised.** §8 is paper; its dependencies (`height-iter'`, Count
   Lemma) are machine-checked.

**Assessment.** §8.1 (height ⊥ value ⟹ linear height-transform) is a solid,
new structural principle and is, I am fairly confident, the crux that was
missing. With it, ε₀ emerges cleanly as `sup_ℓ ω↑↑ℓ` via the finite
type-level tower. I am **cautiously optimistic this is essentially the
proof**, but the function-typed coefficient algebra (caveat 1) is exactly
the kind of step where I have been wrong before, so I am not declaring it
closed until that case analysis is written out (and ideally formalised).

---

## 9. The function-typed case analysis (verification of caveat 1)

The whole proof rests on **two principles** holding through every
combinator. I first state them, then verify each combinator preserves them,
including the function-typed cases. I also re-examined whether §9 secretly
re-imports the broken §7.5 envelope — it does not, and I explain why.

**(P1) Height ⊥ value ⟹ linearity & bounded exponents.** Heights/coefficients
are *never* dialogue values; iteration counts are *always* dialogue values.
Hence (a) a ground input's height enters any result **linearly** (it is
grafted/passed, never used as a count); and (b) any exponent produced by an
iteration is the **count's ordinal size `≤ ω`** (finite, or `ω` for an
oracle-unbounded count), *never* a coefficient. So the only height-affecting
operations are `⊕` (grafting/duplication), `⊗` by a fixed `< ε₀`
coefficient, and `(·)^{⊗(≤ω)}` (an orbit). **Crucially, `c ↦ ω^{c}` and
`c ↦ c^{⊗c}` cannot arise** — those need a height/coefficient in an
exponent, i.e. as a count, which P1 forbids.

**(P2) Counts are magnitudes ⟹ Count Lemma applies.** A count's value is
bounded by its magnitude (`values-≤`/Howard, `≼ F_{<ε₀}`). So an iteration
with a **bounded** count does a bounded (exact) number of steps (Count
Lemma 4a, machine-checked); only an **oracle-unbounded** count triggers the
`ω`-orbit (4b). This is what stops the §7.5 collapse: a *leaf/numeral* count
`η m` does exactly `m` steps, **not** `sup`. §9 reads counts through their
magnitude (P2), never through the envelope `φ_n` (which forgets the index
`m`) — so it is *not* the §7.5 method.

### 9.1 Invariant
For `F : B-Set⟦σ_1⇒⋯⇒σ_p⇒ι⟧`, fully applied to `g⃗`, the ground height is
bounded by a **multilinear form** in the `g_i`'s height-data, with all
coefficients and the constant `< ε₀`, and the magnitude side `≼ F_{<ε₀}`
(Howard). "Tame" = satisfies this hereditarily.

### 9.2 Combinator-by-combinator

* **`η, Zero, Succ, Ω`:** ground or `ι⇒ι`; height-transforms `a↦a`,
  `a↦a`, `a↦a+1`. Linear, coefficient `1`. P1 trivially (no internal
  iteration). ✓
* **`K` (`Ķ x y = x`):** drops `y`; `x`'s data passes unchanged. ✓
* **`S` (`Ş f g x = f x (g x)`):** `x` is **duplicated** (used in `f x …`
  and in `g x`). By IH each path is multilinear; the result's coefficient
  for `x` is the **`⊕`-sum** of the two paths' coefficients — a `⊕`, never
  an exponentiation (P1a). A term has finitely many `S`'s, so finitely many
  duplications: coefficients stay finite `⊕`-sums `< ε₀`. ✓ *(This is the
  case one might fear "blows up"; it does not, because duplication is `⊕`.)*
* **Application `t u`:** substitute `u`'s (tame) data into `t`'s multilinear
  form; coefficients compose by `⊗`, stay `< ε₀`. ✓
* **Recursor `iter' f x n` at `σ = ι`:** §8.2 ground case; coefficient of
  `x` goes `c_f ↦ c_f^{⊗(≤ω)}` (4a finite / 4b `ω`), `< ε₀`. ✓
* **Recursor at function type `σ = ρ⇒…`:** the orbit `F^k(X)` are functions.
  The coefficient that `F` contributes to its argument's coefficient is,
  by P1b, a `(·)^{⊗(≤ω)}` — `F`'s body may iterate its argument an
  oracle-count-many times (`exponent = ω`) but **never coefficient-many
  times**. Hence iterating `F` compounds *exactly* as §8.3:
  `c ↦ c^{⊗ω}` per level, `size_k = c^{⊗ω^k}`, orbit `c^{⊗ω^ω}` — one `ω`
  in the tower per type level. P1b is precisely what forbids the dangerous
  `c ↦ ω^c` that would reach ε₀ in a single level. ✓ (modulo the explicit
  multilinear bookkeeping being written in full)

### 9.3 Does §9 re-import the §7.5 over-estimation?
No, and this is the subtle point. §8.2 bounds a per-step *additive*
contribution by a subterm orbit-sup `s_g` (an envelope-style over-estimate),
which is harmless: `s_g < ε₀` is a fixed constant, and the outer orbit adds
it `ω` times → `s_g·ω < ε₀`. The §7.5 collapse came instead from
over-estimating a **count** (a leaf `η m` treated as `sup`). §9 never does
that: counts are read through magnitude (P2), so a bounded count does
boundedly many steps. **Additive contributions may be loosely bounded;
counts may not — and §9 respects exactly that distinction.**

### 9.4 Verdict
Across all combinators the two principles hold, with the recursor producing
`(·)^{⊗(≤ω)}` per type level and everything else `⊕`/`⊗` with `< ε₀` data.
By induction every closed `t` has `h(dialogue-tree t) < ω↑↑(finite) < ε₀`.

> **I now believe the proof is correct.** The structural reason is clean:
> *height is never a count* (P1), so the recursor can only ever multiply a
> coefficient and take an `ω`-orbit — one tower-level per type-level — and a
> term's finite type level caps the tower below ε₀; *counts are magnitudes*
> (P2), so the §7.5 pathology cannot occur.

**Remaining, honestly:** §9.2's function-type case and §9.1's multilinear
invariant are verified at the level of the coefficient *algebra* (which
operations occur), not yet as a written-out formal induction with the
invariant fully spelled and every inequality discharged. That, plus
formalisation, is what would make it incontrovertible. But I no longer see a
gap in the *mathematics* — P1 and P2 are robust, and they are exactly the
two facts the dialogue interpretation supplies. Subject to the formal
write-up, **the conjecture is proved**, with `h(dialogue-tree t) < ε₀` for
every System T `t`, via: height ⊥ value ⟹ linearity ⟹ per-level `(·)^{⊗ω}`
⟹ finite type-level tower `< ε₀`.

---

## 10. The formal induction — and the exact hierarchy it forces

Writing §9.1 as an actual induction exposes a subtlety that the prose hid,
and fixing it pins down precisely which ordinal hierarchy is required.

### 10.1 Why "tower height in ℕ" is the wrong rank
The natural first attempt is a rank `ρ(M) ∈ ℕ` = "tower height", with `M` of
rank `n` mapping `< ω↑↑m` to `< ω↑↑(m+n)`. **This fails at the orbit.** If
`M_f` has rank `n ≥ 1`, then `M_f^k` has rank `m+kn`, and
`sup_k ω↑↑(m+kn) = ε₀` — the orbit of a tower-raising functional escapes ε₀.
So a ℕ-valued tower rank cannot host the recursor. (This is the same wall as
the very first attempt; worth recording that it recurs here.)

### 10.2 The forced fix: ordinal degrees in the `ω^{(·)}` hierarchy
Use `θ_d = ω^d` with **ordinal** `d < ε₀`, and rank an object's height by a
**degree** `d` with `h ≤ ω^d`. Now the orbit behaves:
* a degree-raise of `+c` (additive) iterates to `+c·k`, with
  `sup_k (d + c·k) = d + c·ω < ε₀` — **`·ω`, not escape.**
* `Ψ(g)=g^{(ω)}` raises degree **multiplicatively**: `d ↦ d·ω`; iterating
  `Ψ` gives `d·ω^k`, orbit `d·ω^ω`; a further level `d·ω^{ω^ω}`, … — each
  type level multiplies the degree by one more `ω`-power, and
  `coefficient at level ℓ = ω^{⊗ω↑↑ℓ}`-ish stays `< ε₀` for finite `ℓ`.

So with **ordinal** degrees the recursor's effect is `d ↦ d · ω^{(ℓ-bounded)}`,
a *multiplication* by an `< ε₀` factor — never `d ↦ ω^d`, which P1 forbids
(that needs the degree, a height-quantity, in an exponent — i.e. as a
count). This is the correct reading of §8.3: the towers live in the
*degree-multiplier*, the degree itself stays `< ε₀`.

### 10.3 The formal invariant
> **Definition.** `Maj^h_ι = Ord`; `Maj^h_{σ⇒τ}` = monotone
> `Maj^h_σ → Maj^h_τ`. `x ◁^h_ι d` iff `h(x) ≤ ω^d`; `F ◁^h_{σ⇒τ} φ` iff
> `∀ x d, x ◁^h_σ d → F x ◁^h_τ φ d`. Combined with the magnitude
> majorant `◁^m` (Howard) as `◁ = ◁^h × ◁^m`.

> **Fundamental Theorem (target).** Every closed `s : σ` has `B⟦s⟧ ◁ μ(s)`
> with `μ(s)`'s degree-data `< ε₀`; hence ground `s` has `h(B⟦s⟧) < ε₀`.

### 10.4 What the induction proves, and the one lemma it needs
* **Generators** `Zero, Succ, Ω, K, S`, **application**: degree-data combine
  by `⊕` (grafting/`S`-duplication) and `⊗` (composition) — **[P]**, exactly
  §9.2, now with `⊕,⊗` on degrees.
* **Recursor, magnitude:** Howard — **[P|H]**.
* **Recursor, height:** by the recursor identity + Count Lemma, the orbit
  multiplies the degree by `ω^{ρ}` where `ρ` is **`f`'s degree-multiplier
  rank**. The whole proof now reduces to:

> **Degree-multiplier lemma (DML).** Every tame functional's degree-raise is
> a *multiplication* by `ω^{ρ}` with `ρ < ε₀`, and the recursor sends
> `ρ ↦ ρ ⊕ (degree-rank of the iterated type)` — so `ρ` is bounded by a
> fixed `< ε₀` ordinal determined by the **type level** of the term.
> **[OPEN — this is the subrecursive-hierarchy core]**

DML is *plausible* because of P1 (no `ω^{degree}`, only `degree · ω^{ρ}`)
and P2 (counts bounded ⟹ orbit length `≤ ω`). Proving it would mean building
a subrecursive-style hierarchy for the **dialogue degree-multipliers**.

**Correction (important).** DML is about dialogue-tree *rank*, and it is
**not** Howard's theorem and not citable from it. Howard 1970 assigns
ordinals bounding *value/reduction* complexity, with no dialogue trees;
and §0 shows dialogue height is **independent** of value magnitude
(`height ⊥ value`). So Howard legitimately discharges the **magnitude**
side (§2 — magnitudes are values), but supplies **nothing** for the height
side (DML). Earlier wording here that called DML "Howard's theorem
transported to tree rank" was wrong: the transport is exactly the open
content, and there is, to our knowledge, no extant theorem to cite for it.

### 10.5 Honest final status of the proof attempt
* The **informal** proof (§8–9: P1 ⟹ linearity ⟹ per-level `·ω^{ρ}` ⟹
  type-level-bounded degree `< ε₀`) I find suggestive, and I believe the
  theorem is **true** — but §8–9 are not a verified proof.
* The **formal** induction (§10) is complete except for **DML**, the orbit
  bound on dialogue height, which is **genuinely open and not citable**
  (the magnitude side is Howard; the height side is new).
* So the certifiable endpoint is a conditional: **orbit bound ⟹ recursor
  height bound** (machine-checked in `DialogueTreeHeight.Conditional`), with
  the orbit bound (DML) an unproved, dialogue-specific hypothesis. P1/P2 are
  the genuine new content and make DML plausible, but do not prove it.

I am **not** claiming the conjecture proved, nor that DML is discharged: it
is reduced to a single open lemma about dialogue-tree rank, with the
elementary engine (L1–L3, Count Lemma, operator algebra, and the conditional
recursor bound) machine-checked beneath it.
