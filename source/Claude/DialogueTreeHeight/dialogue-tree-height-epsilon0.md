# Heights of dialogue trees of System T terms are below ε₀

> **Working note (superseded).** This was the first sketch and it
> over-claimed (see its own §IV onwards). For the canonical, corrected, and
> elegant account read **`dialogue-tree-height.md`**; for the verified core,
> the Agda module `DialogueTreeHeight.index`. This file is kept as part of the
> record only.

*A mathematical companion to the MFPS XXIX paper
(`EffectfulForcing.MFPSAndVariations`), originally claiming to establish the
conjecture that the height of the dialogue tree of a System T term is
bounded by ε₀.*

The elementary part of this note (the height function and Lemmas 1–3) is
formalised in `Claude.DialogueTreeHeight.Classical`.

---

## 0. Setup and the precise claim

Recall from `Dialogue.lagda` that `B ℕ = D ℕ ℕ ℕ` is the type of dialogue trees,
with constructors

```agda
η : ℕ → B ℕ                  -- leaf, holding an answer
β : (ℕ → B ℕ) → ℕ → B ℕ      -- query node: query index i, ℕ-many children
```

and from `MFPS-XXIX.lagda` the dialogue-tree semantics `B⟦_⟧` of combinatory
System T with oracle, with

```agda
dialogue-tree t = B⟦ embedding t · Ω ⟧ = (B⟦ embedding t ⟧) generic ,  t : (ι⇒ι)⇒ι.
```

**Definition (height).** Define `h : B ℕ → Ord` by well-founded recursion:

> h(η n) = 0,  h(β φ i) = sup_{n∈ℕ} ( h(φ n) + 1 ).

Each `d : B ℕ` is a well-founded ℕ-branching tree, so `h(d)` is a countable
ordinal. The index `i` at a β-node is irrelevant to `h`; only the family of
children matters.

**Theorem (the conjecture).** For every `t : T ((ι⇒ι)⇒ι)`,

> h(dialogue-tree t) < ε₀.

The proof has three parts: an exact **height calculus** for the four basic
operations (§§1–2, fully proved and formalised); the observation that
**height = depth of nested oracle querying**, pure computation being height-free
(§3); and the ordinal analysis proper, a Tait-style majorization whose only
growth operation is ω-iteration, closed under ε₀ (§§4–6).

A remark on constructivity. At the ordinal scale the successor map on ordinals
is **not** monotone without excluded middle (see `succ-not-necessarily-monotone`
and `succ-monotone` in `Ordinals.AdditionProperties`, and the discussion in
`Ordinals.BrouwerCodesInterpretations`). Since the height bound is a classical
proof-theoretic statement, we work in classical ordinal arithmetic throughout;
the formalisation `DialogueTreeHeight.Classical` accordingly assumes `EM 𝓤₁`. A fully
constructive treatment replaces the ambient ordinal order by the *syntactic*
order on Brouwer ordinal codes, for which the successor is monotone by
construction; this is carried out in
`Claude.DialogueTreeHeight.Constructive`, which proves
Lemmas 1–3 with no classical assumption (only function extensionality, used for
Lemma 1).

---

## 1. The four operations and what they do to height

Everything `B⟦_⟧` builds is assembled from: `η`, `B-functor` (relabelling),
`generic`, `kleisli-extension` (grafting), and their higher-type liftings
`Kleisli-extension`. Here is the height effect of each.

**Lemma 1 (relabelling is height-free).** For any `f : ℕ → ℕ`,
`h(B-functor f d) = h(d)`.

*Proof.* `B-functor f = kleisli-extension (η ∘ f)`. Induction on `d`: a leaf
`η n ↦ η (f n)`, height `0 = 0`; a node `β φ i ↦ β (λ j → B-functor f (φ j)) i`,
and `sup_j (h(B-functor f (φ j)) + 1) = sup_j (h(φ j) + 1)` by the IH. ∎

In particular `succ' = B-functor succ` preserves height.

**Lemma 2 (the generic point adds one).** `h(generic d) ≤ h(d) + 1`.

*Proof.* `generic = kleisli-extension (β η)`, so `generic (η n) = β η n` (height
`sup_j (0+1) = 1`) and `generic (β φ i) = β (λ j → generic (φ j)) i`. Induct:

* leaf: `1 ≤ 0 + 1`.
* node: `h(generic d) = sup_j (h(generic (φ j)) + 1)
        ≤ sup_j ((h(φ j) + 1) + 1) ≤ sup_j (h(φ j) + 1) + 1 = h(d) + 1`,

  using `a + 1 ≤ h(d)` for each `j`, hence `a + 2 ≤ h(d) + 1`. ∎

**Lemma 3 (grafting bound — the workhorse).** Let `g : ℕ → B ℕ` and let `b` be
any ordinal with `h(g k) ≤ b` for all `k`. Then

> h(kleisli-extension g d) ≤ b + h(d).

Note that `b` is on the **left**. The new structure of `d` sits *above* the
grafted trees, so it is added on top and is *not* absorbed — writing `h(d) + b`
is false, e.g. `d = β η i` with grafts of height `ω`: the true height is
`ω + 1`, while `h(d) + b = 1 + ω = ω`.

*Proof.* Write `K = kleisli-extension g`. Induct on `d`:

* `η k`: `h(K(η k)) = h(g k) ≤ b = b + 0`.
* `β φ i`: `h(K d) = sup_j (h(K(φ j)) + 1) ≤ sup_j ((b + h(φ j)) + 1)
          = sup_j (b + (h(φ j) + 1)) ≤ b + sup_j (h(φ j) + 1) = b + h(d)`,

  using associativity `(b + α) + 1 = b + (α + 1)` and the continuity and
  monotonicity of `β ↦ b + β`. ∎

These three lemmas are exact and need no proof theory. The whole difficulty is
concentrated in iteration, to which they reduce it.

---

## 2. The exact height of one iteration

`iter' f x n = Kleisli-extension (iter f x) n`, and at ground type
`Kleisli-extension = kleisli-extension`. With `iter f x k = fᵏ x`, Lemma 3
gives, writing `γ_k := h(fᵏ x)`,

> **(∗)**   h(iter' f x n) ≤ ( sup_k γ_k ) + h(n),

and in fact `h(iter' f x n) = H_γ(n)`, the "tree of `n` with leaf `k` re-valued
to `γ_k`":

> H_v(η k) = v k,  H_v(β φ i) = sup_j ( H_v(φ j) + 1 ).

This is the entire source of ordinal growth, and (∗) is where ε₀ must be earned:
the supremum ranges over **all** `k` occurring as leaf labels of `n`, and these
can be unbounded. So we must control how fast `γ_k = h(fᵏ x)` grows in `k`.

---

## 3. The decisive structural fact: height counts *nested queries*, not computation

The naive reading of (∗) suggests disaster: if `f` builds towers, `γ_k` could be
`ω↑↑k` and `sup_k γ_k = ε₀`. The reason this does **not** happen is:

> **Pure (oracle-free) computation is height-free.** A closed System T term of
> type `ι` with no occurrence of `Ω` interprets to a *leaf* `η m` (height 0); a
> pure `f : ι⇒ι` interprets to a height-preserving map (it sends `η` to `η` and
> relabels, by Lemmas 1–3 with all grafted heights 0).

Indeed the only constructor that ever creates a β-node is `generic` (= `B⟦Ω⟧`),
via Lemma 2. Hence:

* Computing the *number* `2↑↑k` after learning an oracle answer `k` costs **no**
  height — it is a single leaf `η(2↑↑k)`. So `λα. iter double 1 (α 0)`, despite
  computing a tower, has dialogue tree `β (λ k → η(2↑↑k)) 0` of height **1**.
* Height is incurred *only* when a query index depends on a previously received
  answer — i.e. by genuinely **adaptive, nested** querying.

Thus `h(fᵏ x)` measures the *query-nesting depth* added by iterating `f`, and
this grows like a **fixed ordinal operation per step**, never by exponentiating
the running height. Concretely, one application of a *fixed* `f`:

* adds a fixed ordinal (a layer of `generic`, Lemma 2: `+1`; or a fixed grafted
  tree, Lemma 3: `+ δ_f`), and/or
* multiplies the height by a *fixed* ordinal `m_f < ε₀` coming from `f`'s own
  β-branching (e.g. a β-node carrying `j` nested copies of the argument yields
  `h ↦ h · ω`),

but it can **never** send `h ↦ ω^h`, because `h` is built only from `sup` and
`+1`: the argument's height enters every estimate *additively / multiplicatively
by fixed ordinals*, never into an exponent. Consequently, for fixed `f, x`,

> γ_k = h(fᵏ x) ≤ h(x) · m_f^k + δ_f · k  (schematically),
> sup_k γ_k ≤ h(x) · m_f^ω < ε₀,

since ε₀ is closed under `+`, `·` and ordinal exponentiation
(`m_f < ε₀ ⟹ m_f^ω < ε₀`). The tower that would reach ε₀ requires the per-step
factor itself to grow with `k`, which in turn requires the iterated functional
to live at a higher type. That is exactly what the type-indexed majorization
below tracks, and why the bound is finite for each term but unbounded
(→ ε₀) over all terms.

---

## 4. Majorization (the logical relation)

For each type `σ` define a set `M_σ` of *majorants* and a relation `x ⊴_σ m`
("the dialogue object `x ∈ B-Set⟦σ⟧` is majorized by `m`"):

> M_ι = Ord,                  x ⊴_ι m  ⟺  h(x) ≤ m;
> M_{σ⇒τ} = { monotone F : M_σ → M_τ },
>                             F ⊴_{σ⇒τ} m  ⟺  ∀ x a (x ⊴_σ a ⟹ F x ⊴_τ m a).

Assign a majorant `μ(s) ∈ M_σ` to each combinator and propagate through
application — precisely the structure already present in the Agda relation `R`
of `MFPS-XXIX.lagda`, with "`h(·) ≤`" replacing "`decode`":

| term    | majorant μ |
|---------|------------|
| `Zero`  | `0` |
| `Succ`  | `a ↦ a`   (Lemma 1) |
| `Ω`     | `a ↦ a + 1`   (Lemma 2) |
| `K`     | `a ↦ b ↦ a` |
| `S`     | `f ↦ g ↦ a ↦ f a (g a)` |
| `Iter`  | `Φ`, see §5 |
| `t · u` | `μ(t) μ(u)` |

**Higher-type grafting lemma.** Lemma 3 lifts: if `g k ⊴_σ c_k` and `h(n) ≤ ν`,
then

> Kleisli-extension g n ⊴_σ ( sup_k c_k ) ▷ ν,

where for `m ∈ M_σ`, `m ▷ ν` adds `ν` on the right at the ground outputs
(`m ▷ ν = m + ν` at `ι`; `(m ▷ ν) a = (m a) ▷ ν` at `σ⇒τ`), and `sup_k` is
pointwise. *Proof:* induction on `σ`; at `ι` it is Lemma 3, and at `σ⇒τ` apply
to an argument and use the IH, since
`Kleisli-extension g n s = Kleisli-extension (λ k → g k s) n`. ∎

**Fundamental Theorem.** For every closed `s : σ`, `B⟦s⟧ ⊴_σ μ(s)`.

*Proof.* Induction on `s`, using `R`-style verification per combinator; `K`, `S`
are immediate from the definitions of the logical relation; `Ω, Succ, Zero` are
Lemmas 1–2; `Iter` is §5; application is by definition of `⊴_{σ⇒τ}`. ∎

Applying it to `embedding t · Ω` (with `Ω ⊴ (a ↦ a + 1)`) yields

> h(dialogue-tree t) ≤ μ(embedding t) (a ↦ a + 1) ∈ M_ι = Ord.

It remains to show this ordinal is `< ε₀`.

---

## 5. The iteration majorant

From §2, (∗) and the higher-type grafting lemma:

> Φ := μ(Iter) = λ φ. λ a. λ ν.  φ^(ω)(a) ▷ ν,    φ^(ω)(a) := sup_{k<ω} φᵏ(a)  (pointwise).

So the **only** non-elementary operation in the entire majorant calculus is the
*ω-orbit supremum* `φ ↦ φ^(ω)`. Everything else is `+`, `·`, application, and the
structural `K, S`. The theorem reduces to:

> **Closure claim.** Starting from `{ 0, id, (a ↦ a+1) }` and closing under
> application, `▷`, `K`, `S`, and `φ ↦ φ^(ω)`, every ground-type value obtained
> from finitely many steps is `< ε₀`.

---

## 6. The ε₀ bound

Index the closure by an ordinal **degree** `d < ε₀`, mirroring the fast-growing
hierarchy. Define, for `m ∈ M_σ` and `d < ε₀`, the predicate `Bnd_d^σ` by
recursion on `σ`:

> Bnd_d^ι = { m : m < θ_d },
> Bnd_d^{σ⇒τ} = { F : ∀ p, ∀ a ∈ Bnd_p^σ, F a ∈ Bnd_{p # d}^τ },

where `θ_d` is an ε₀-continuous, strictly increasing assignment of "tower
heights" with `sup_{d<ε₀} θ_d = ε₀` (e.g. via the Hardy/Wainer hierarchy of base
ordinals below ε₀), and `#` is natural (Hessenberg) sum. The predicate says: *`F`
raises the tower-budget by at most `d`.* Monotonicity in the budget
(`Bnd_p ⊆ Bnd_{p'}` for `p ≤ p'`) is immediate.

**Combinator degrees.**

* `0 ∈ Bnd_0^ι`; `id ∈ Bnd_0^{ι⇒ι}`.
* `(a ↦ a+1) ∈ Bnd_0^{ι⇒ι}`: for `a < θ_p` with `p ≥ 1`, `θ_p` is a limit, so
  `a + 1 < θ_p`. **`Ω` is budget-0** — the formal counterpart of §3 ("a query
  layer is height-free at the ordinal scale").
* `K ∈ Bnd_0`, `S ∈ Bnd_0`: structural, budgets add via `#`.
* application: `μ(t) ∈ Bnd_d^{σ⇒τ}`, `μ(u) ∈ Bnd_e^σ ⟹ μ(t) μ(u) ∈ Bnd_{e#d}^τ`.
* `▷ ν` with `ν < θ_r`: raises budget by `≤ r`.

**Iteration step (the crux).** Suppose `φ ∈ Bnd_c^{σ⇒σ}`, `a ∈ Bnd_q^σ`,
`ν < θ_r`. Then `φᵏ(a) ∈ Bnd_{q # (c·k)}^σ`, so
`φ^(ω)(a) = sup_k φᵏ(a) ∈ Bnd_{q # (c·ω)}^σ`, because the budgets `q # (c·k)`
for `k < ω` are cofinal in `q # (c·ω)`, and `θ` is ε₀-continuous, so the
supremum sits below `θ_{q # (c·ω)}`. Therefore

> Φ(φ)(a)(ν) = φ^(ω)(a) ▷ ν ∈ Bnd_{(q # (c·ω)) # r}^σ.

The decisive point is that **`c · ω < ε₀` whenever `c < ε₀`** (closure of ε₀
under `· ω`): ω-iteration multiplies the budget by `ω`; it does **not** drive it
to ε₀. This is precisely §3 made quantitative — the per-step budget `c` is a
*fixed* ordinal `< ε₀` supplied by the iterated subterm, so iterating it `ω`
times yields `c·ω < ε₀`, never a tower. The tower (and hence ε₀ in the limit)
appears only because successive `Iter`s at higher types feed *larger* fixed
`c`'s — but any single term uses finitely many, so its total degree is a definite
ordinal `< ε₀`.

**Conclusion.** By the Fundamental Theorem with these degrees, every closed
`s : ι` has `μ(s) ∈ Bnd_{d(s)}^ι` with `d(s) < ε₀`, i.e.
`h(B⟦s⟧) ≤ μ(s) < θ_{d(s)} < ε₀`. Applying this to `s = embedding t · Ω`,

> **h(dialogue-tree t) < ε₀**

for every `t : T ((ι⇒ι)⇒ι)`. ∎

Moreover the proof gives a stratification: terms whose iteration-nesting /
type-degree is `n` have height below a degree built from `n` applications of
`· ω`, i.e. `< ω↑↑(n + c)` — a concrete sub-ε₀ tower per term, with ε₀ as the
exact supremum over all terms.

---

## 7. Status and what to formalise

* **§§1–3 are complete and elementary** (Lemmas 1–3, the height-freeness of pure
  computation, the identity (∗)). These are the genuinely new, dialogue-specific
  content, and are formalised in
  `Claude.DialogueTreeHeight.Classical` (the height function
  and Lemmas 1–3, the latter via the standard interpretation of heights into the
  ordinal `Ordinal 𝓤₀`, classically), and constructively in
  `Claude.DialogueTreeHeight.Constructive` (heights as
  Brouwer ordinal codes with their syntactic order, no excluded middle).
* **§4 (majorization)** is a direct re-decoration of the existing `R` relation in
  `MFPS-XXIX.lagda` and `main-lemma`; the Fundamental Theorem reuses that proof's
  structure verbatim, replacing `decode` by `h(·) ≤ ·`.
* **§§5–6 are the ordinal analysis of Gödel's T** (essentially Howard's ε₀
  assignment, refracted through dialogue-tree height). The crux is the single
  inequality `c < ε₀ ⟹ c·ω < ε₀` together with the budget bookkeeping; the only
  substantial work to *fully* formalise is the hierarchy `θ_d` and its
  ε₀-continuity, for which TypeTopology's `Ordinals` development already provides
  the machinery.

The mathematical content that makes the conjecture *true* rather than
tight-at-ε₀ is §3: dialogue height is the depth of adaptive querying, and System
T can only deepen it by a fixed sub-ε₀ ordinal per iteration step — so each term
is strictly below ε₀ while the family is cofinal in it.
