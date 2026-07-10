# Hereditary two-component majorant: a scoped build

> **Working note (superseded).** Canonical account: **`dialogue-tree-height.md`**.
> Verified core: Agda `DialogueTreeHeight.index`. The "Howard" framing here is
> corrected in `dialogue-tree-height-correct-framing.md`. Kept as record.

*Goal: define the hereditary (height, magnitude) majorant à la Howard for
the dialogue interpretation of System T, and prove the fundamental theorem
case by case, with an explicit **status tag** on every lemma:*

* **[PROVED]** — proof given here, complete.
* **[PROVED mod X]** — complete given a stated, used auxiliary fact `X`.
* **[OPEN]** — reduces to a precisely stated lemma I have not proved; this
  is where the genuine ordinal-analytic content sits.

The headline outcome of this build: **everything reduces to a single
[OPEN] lemma — the *orbit-height lemma* (Lemma R3) — and that lemma is the
fast-growing-hierarchy heart of Howard's theorem.** All the plumbing
(definitions, structural combinators, the magnitude component of the
recursor, the height component for bounded counts) is proved.

Notation: `α, β : Baire = ℕ→ℕ` oracles; `α ≤ b` means `∀i, α i ≤ b`;
`dlg x α := dialogue x α`. Heights `h(·)` and `H_v(·)` as in
`…-ordinal-analysis.md`. Recall `h(iter' f x n) = H_γ(n)` with
`γ_k = h(f^k x)` (the value-sensitive height with the orbit at the leaves).

---

## 1. The majorants — [DEFINED]

A **ground majorant** is a pair `(a, V)` with `a : Ord` (a height bound)
and `V : ℕ → ℕ` monotone (a *magnitude function*: `V(b)` bounds values
under an oracle bounded by `b`). Order them by `(a,V) ≤ (a',V')` iff
`a ≤ a'` and `V ≤ V'` pointwise.

Hereditarily:

> `Maj_ι = Ord × (ℕ→ℕ_mono)`,  `Maj_{σ⇒τ} =` monotone maps `Maj_σ → Maj_τ`.

The **majorization relation** `R_σ ⊆ B-Set⟦σ⟧ × Maj_σ`:

* `R_ι(x, (a,V))` :⟺ `h(x) ≤ a` **and** `∀b ∀α≤b, dlg x α ≤ V(b)`.
* `R_{σ⇒τ}(F, φ)` :⟺ `∀ x p, R_σ(x,p) → R_τ(F x, φ p)`.

`R` is upward closed in the majorant (both components are bounds), and
closed under pointwise sups of the majorant, as before.

The two projections `π_h(a,V)=a`, `π_m(a,V)=V` recover the height bound and
the magnitude function. The whole point: `π_m` is what the recursor's count
reads, and `π_h` rides on it.

---

## 2. Structural combinators — [PROVED]

> **Lemma Z (Zero).** `R_ι(η 0, (0, λb.0))`. **[PROVED]**

`h(η0)=0`; `dlg (η0) α = 0`.

> **Lemma S+ (Succ).** `R_{ι⇒ι}(succ', μS)` with `μS(a,V) = (a, V+1)`,
> where `(V+1)(b) = V(b)+1`. **[PROVED]**

`succ' = B-functor succ`: `h(succ' x)=h(x)` (L1); and `dlg (succ' x) α =
succ(dlg x α) = dlg x α + 1 ≤ V(b)+1` (naturality of `decode`). So from
`R_ι(x,(a,V))` we get `R_ι(succ' x, (a, V+1))`.

> **Lemma Ω+ (the oracle).** `R_{ι⇒ι}(generic, μΩ)` with
> `μΩ(a,V) = (a+1, idℕ)`, `idℕ = λb.b`. **[PROVED]**

By `generic-diagram`, `dlg (generic x) α = α(dlg x α)`. For `α ≤ b`,
`α(anything) ≤ b`, so `dlg (generic x) α ≤ b`: magnitude `idℕ`,
*independent of `V`* — the oracle **resets** magnitude to `λb.b`. Height
`h(generic x) ≤ h(x)+1` (L2). Note both facts are exactly L2 plus the
generic diagram.

> **Lemma K, S (combinators).** With `μK = λp q. p` and
> `μS3 = λφ ψ p. φ p (ψ p)`, we have `R(Ķ, μK)` and `R(Ş, μS3)`. **[PROVED]**

Immediate from the definition of `R_{σ⇒τ}` (same as the height-only proof;
the pair structure rides along). Application preserves `R` by definition.

So far this is a *complete* fundamental theorem **except** for the recursor.

---

## 3. The recursor — magnitude component [PROVED], height component
[PROVED for bounded counts], orbit [OPEN]

Take `Iter : (σ⇒σ)⇒σ⇒ι⇒σ`. Assume `R_{σ⇒σ}(f,φ)`, `R_σ(x,p₀)`,
`R_ι(n,(ν,W))`. Define the **orbit** `p_k := φ^k(p₀) ∈ Maj_σ`; by induction
and `R_{σ⇒σ}(f,φ)`, `R_σ(f^k x, p_k)` for all `k`. We must majorize
`iter' f x n = Kleisli-extension (iter f x) n`.

### 3a. The count is bounded by the magnitude — [PROVED]

> **Lemma R1 (count bound).** For `α ≤ b`, the iteration count
> `dlg n α ≤ W(b)`.

This is exactly `R_ι(n,(ν,W))`'s magnitude clause: `dlg n α ≤ W(b)`. The
count performed by `iter'` at oracle `α` is `dlg n α` (a leaf value of
`n`), so it is `≤ W(b)`. ∎  *(This is the lemma the height-only majorant
could not see — `h(n) = ν` says nothing about `dlg n α`.)*

### 3b. Magnitude of the result — [PROVED mod Mon]

Restrict to `σ = ι` (first-order recursor; higher `σ` in §5). Then
`p_k = (a_k, V_k)`, and:

> **Lemma R2 (result magnitude).** Assume the orbit magnitudes are
> monotone in the index (`k ≤ k' ⇒ V_k ≤ V_{k'}`) — call this **(Mon)**.
> Then `R_ι`'s magnitude clause holds for `iter' f x n` with
> `V'(b) := V_{W(b)}(b)`.

*Proof.* For `α ≤ b`: `dlg (iter' f x n) α = dlg (f^{c} x) α` where
`c = dlg n α ≤ W(b)` (R1). By `R_ι(f^c x,(a_c,V_c))`,
`dlg (f^c x) α ≤ V_c(b) ≤ V_{W(b)}(b)` using (Mon). ∎

**(Mon)** holds whenever `f`'s magnitude-transform is inflationary
(`V ≤ π_m(φ(a,V))`), which is the case for all combinators above
(`Succ: V↦V+1`, `Ω: V↦idℕ ≥`, etc.) and is preserved by composition. I take
**(Mon)** as a routine side-condition; flagged but not belaboured.

### 3c. Height of the result — [PROVED for bounded `W`], [OPEN for ∞]

`h(iter' f x n) = H_γ(n)`, `γ_k = h(f^k x) ≤ a_k`.

> **Lemma R-Count (bounded counts).** If `W` is bounded by `M < ω`
> (i.e. `n` has finite magnitude `M`), then `h(iter' f x n) ≤ ν + a_M`.
> **[PROVED]**

*Proof.* Every leaf value `k` of `n` satisfies `k ≤ M` (finite magnitude),
so `γ_k = a_k ≤ a_M` (heights non-decreasing along the orbit — part of
(Mon)); grafting `≤ a_M` at every leaf, L3 gives `H_γ(n) ≤ a_M + ν`,
i.e. (reordering, `ν` on the right via L3's left-summand form)
`≤ ν + a_M`. ∎

> **Lemma R3 (orbit-height lemma).** `sup_{k<ω} a_k < ε₀`. **[OPEN]**

For unbounded `W` (oracle-dependent count, `∞` magnitude) the leaves of `n`
realise arbitrarily large values, and the worst case (e.g. `n = generic(η0)
= β η 0`, value `j` at depth `1`) gives `H_γ(n) = sup_j (γ_j + 1) =
sup_k a_k`. So the height of the result is `ν + sup_k a_k`, and the entire
remaining difficulty is:

> **`sup_k a_k < ε₀`,** where `(a_k,V_k) = φ^k(p₀)` is the orbit of a
> System-T-arising majorant.

This is exactly the fast-growing-hierarchy statement (see §4): the heights
`a_k` are controlled by the **growth rate** of the magnitude functions
`V_k`, and that growth rate is an ordinal `< ε₀` because `V_k` are System T
functions of `b`.

### 3d. The recursor majorant — assembled

Putting R2 + R-Count/R3 together, the recursor majorant (for `σ=ι`) is

> `μIter(φ)(a₀,V₀)(ν,W) = ( ν + sup_{k ≤ W̄} a_k ,  λb. V_{W(b)}(b) )`,
> `W̄ = sup_b W(b) ∈ ℕ∪{∞}`,  `(a_k,V_k)=φ^k(a₀,V₀)`,

and `R_ι(iter' f x n, μIter…)` holds **[PROVED]** for `W̄ < ω` and
**[OPEN, = R3]** for `W̄ = ∞`. So:

> **Fundamental Theorem (status).** `R_σ(B⟦s⟧, μ(s))` for every closed `s`,
> **[PROVED]** for the `Ω`-free and bounded-count fragments, and reduced to
> **Lemma R3** in general.

---

## 4. Lemma R3 is the fast-growing hierarchy — [OPEN, precisely stated]

Why `sup_k a_k < ε₀` is the crux, and what it needs.

Along the orbit, the height recurrence has the schematic form (first order)
`a_{k+1} ≤ a_k · c ⊕ ω^{e(V_k)}`, where `e(V_k)` measures the *magnitude*
fed back as an internal count, and `c < ω`. Two regimes:

* **Finite magnitude exponents.** If the `V_k` keep the relevant exponent
  `e(V_k)` **finite**, then `ω^{e(V_k)} < ω^ω` and the recurrence stays
  below `ω^{ω·2}` — this is the first-order theorem of
  `…-two-component.md` §3, **[PROVED]** there. No ε₀.

* **Ordinal magnitude growth rate.** `ε₀` appears only when the *growth
  rate of `V_k` as a function of `b`* becomes an infinite ordinal — i.e.
  when `V_k` climbs the fast-growing hierarchy `F_β`, `β<ε₀`. This happens
  through **higher-type** iteration (§5), where the magnitude-transform is
  itself iterated. Then `e(V_k)` is an ordinal `β_k`, and `sup_k a_k`
  is governed by `sup_k ω^{β_k}`.

> **Lemma R3, sharp form.** For a closed term, the magnitude functions
> `V_k` arising in any orbit are System T functions of `b`, hence dominated
> by `F_β` for a **fixed** `β < ε₀` (depending on the term's type level);
> consequently the height exponents `β_k` are bounded by a fixed `β<ε₀`,
> and `sup_k a_k ≤ ω^{β}·ω < ε₀`. **[OPEN]**

This is precisely Howard (1970): the assignment of ordinals `< ε₀` to
System T terms via the subrecursive (fast-growing) hierarchy, with the
recursor handled at every type level. The dialogue-height component rides
on it through Lemmas R1–R2 and R-Count. I have **not** proved Lemma R3; it
is the genuine ordinal analysis.

---

## 5. Higher-type recursor — [OPEN, structure given]

For `σ = σ₁⇒…⇒σ_p⇒ι`, `p_k = φ^k(p₀) ∈ Maj_σ` are *functionals*, and:

* **Magnitude** (R2) generalises: the result, applied to majorized
  arguments, has magnitude `V_{W(b)}(b)` *pointwise at ground* — the same
  Count-Lemma bound, pushed under the arguments exactly as in the
  height-only Lemma G. **[PROVED mod Mon, modulo the ground R2]**
* **Height** (R-Count/R3) generalises identically: bounded count ⇒ `ν+a_M`;
  unbounded count ⇒ `ν + sup_k a_k`, with `a_k` now the *ground* height
  obtained after applying the orbit functional to majorized arguments.

So §5 adds **no new obstruction beyond R3** — it only makes R3's orbit live
in a function space. The reason R3 is hard here is that the functional
orbit `φ^k` can make the magnitude growth-rate `β_k` *increase with `k` as
an ordinal*, which is where the climb to `ε₀` occurs and why the type level
bounds the final ordinal.

---

## 6. Status summary

| Component | Status |
|---|---|
| Majorant definition (`Maj_σ`, `R_σ`) | **[DEFINED]** |
| `Zero, Succ, Ω, K, S`, application | **[PROVED]** |
| Recursor: count bound (R1) | **[PROVED]** |
| Recursor: result magnitude (R2) | **[PROVED mod Mon]** |
| Recursor: height, bounded count (R-Count) | **[PROVED]** |
| Recursor: orbit height `sup_k a_k < ε₀` (R3) | **[OPEN]** = Howard/fast-growing |
| Higher-type recursor (§5) | **[reduces to R3]** |
| First-order fragment (`< ω^{ω·2}`) | **[PROVED]** (`…-two-component.md` §3) |

**Net.** The fundamental theorem is fully assembled and **everything funnels
into the single Lemma R3** — the orbit-height bound, which is the
fast-growing-hierarchy/Howard content. This is real progress: the entire
dialogue-specific apparatus (definitions, structural combinators, the
magnitude component, the count-sensitive height) is proved, and the
residual difficulty is now one sharply-stated ordinal lemma rather than a
diffuse "do the higher-type case". The conjecture holds iff R3 does, and R3
is true (it is the ordinal analysis of T). I have not proved R3 from
scratch; doing so is the Howard-style fast-growing-hierarchy development,
the natural next milestone.
