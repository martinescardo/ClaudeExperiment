# The height of a dialogue tree
### How deeply can a System T functional interrogate its oracle?

*This is the canonical account. The other `dialogue-tree-height-*.md` files
in this directory are the working notes that led here — kept as a record,
but superseded by this one. The mathematics that is **proved** is
machine-checked in the Agda modules `DialogueTreeHeight.*` (all `--safe`, no
postulates); a guided tour is `DialogueTreeHeight.index`.*

---

## The picture

A closed System T term `t : (ι ⇒ ι) ⇒ ι` denotes a functional: feed it a
sequence `α : ℕ → ℕ` and it returns a number. Being a *program*, it learns
about `α` only by **asking** — evaluating `α(i)` at points `i` of its
choosing — and it is **adaptive**: which point it asks about next may depend
on the answers it has already heard.

The complete record of this interrogation is a tree:

* a **leaf** `η n` — the term has stopped asking and returns `n`;
* a **query node** `β φ i` — the term asks for `α(i)`, and for each possible
  answer `j ∈ ℕ` the interrogation continues as the subtree `φ(j)`.

This is the **dialogue tree** of `t` (Escardó 2013). Because `t` is total,
every branch terminates: the tree is well-founded. But a query node has
*infinitely many* children — one per possible answer — so the tree, while
well-founded, may be infinitely wide, and its **height** is a genuine
countable **ordinal**:

> `h(η n) = 0`,    `h(β φ i) = sup_j ( h(φ j) + 1 )`.

The height measures the deepest *adaptive* chain of questions — how many
answers must come back, each shaping the next question, before the term can
finish.

> **Escardó's conjecture.** For every System T term, this height is `< ε₀`.

---

## Why this is ordinal analysis

An infinitely-branching well-founded node — "for each answer `j`, here is
the continuation" — is exactly an instance of the **ω-rule** of infinitary
proof theory. So a dialogue tree is an infinitary derivation, a strategy in
the sense of Schütte and Tait, and its height is the ordinal rank of that
derivation. Escardó and Oliva make this literal: their `Dialogue-to-Brouwer`
translation turns a dialogue tree into a **Brouwer tree**, which *is* an
ordinal notation.

The conjecture thus lives in the tradition of **Gentzen** — who showed `ε₀`
is the proof-theoretic ordinal of arithmetic — and **Tait**, who analysed
System T by computability and infinitary terms. The bound `ε₀` is precisely
what that tradition predicts.

(It is *not*, despite the resemblance, a corollary of **Howard's** 1970
assignment of ordinals to System T terms. Howard bounds the *values* a term
computes and its reduction length; the height of the dialogue tree is
independent of those — see the next section. Borrowing Howard here would be
a category error.)

---

## The heart: depth cannot see itself

Why should the depth be bounded? A program may loop, loops may nest, and the
oracle may answer with arbitrarily large numbers. What stops the
interrogation from descending past every countable ordinal?

Watch the program run. It does two separable things. It **computes with
answers** — adding, comparing, feeding them into further loops; all of this
produces *numbers*. And it **asks questions** — and the way each question
depends on the last answer is what builds the tree.

Here is the asymmetry on which everything turns:

> **A program reads and writes answers, but it can only ever write to the
> tree — never read it.**

The tree is the *transcript* of the conversation. We, watching from
outside, can measure its depth; the program, speaking from inside, cannot —
it has no expression for "how deep am I." So when a loop runs "`n` times",
`n` is a *number the program is holding* — an answer, or something computed
from answers. It is **never** the current depth of the tree, because the
program cannot name that.

The consequence is decisive. A function can deepen the tree by a *fixed*
amount, or run a loop that deepens it *(some answer)*-many times. But **how
much it deepens can never depend on how deep the tree already is.** In
ordinal terms, if a function sends an input of depth `δ` to an output of
depth `f(δ)`, then `f` is **linear**:

> `f(δ) ≤ δ · c + d`,    with `c, d < ε₀` read off from the *answers*, never
> from `δ`.

Depth can be added to, and scaled by a constant — but never raised to a
power of itself, never used as its own loop counter. **Depth cannot
bootstrap.**

And this single fact bounds the tower. The only operation that could outrun
`ε₀` in finitely many steps is one that *exponentiates* depth; linearity
forbids it. (The concrete witness that depth ⊥ value: the tree
`iter generic base (generic (η 0))` has height `ω` while every value it
computes stays `≤ b` whenever the oracle does. Deep interrogation, tiny
numbers.)

---

## The law of iteration

The mechanism has an exact, and rather beautiful, expression. Iterate a
function `f` a number of times given by a tree `n`, from a start `x`. The
subtlety: `n` is itself a dialogue tree — it may *ask the oracle* how many
times to loop — so the count is not one number but a tree of possible
counts. The height obeys one clean law (machine-checked, `height-iter'`):

> `h( iterate f, n times, from x )  =  H_n( m ↦ h(f^m x) )`.

Here `H_n` feeds a *schedule* — an ordinal for each possible count `m` —
through the count-tree `n` itself: at a leaf `m` it reads the schedule at
exactly `m`; at a query node it takes the supremum over the oracle's
answers. The two regimes live in one formula:

* if `n` is a **numeral** `m` (never consults the oracle), the height is
  *exactly* `h(f^m x)` — the loop runs `m` times, no more;
* if `n` **asks the oracle** (the worst case), the height is the *supremum*
  `sup_m h(f^m x)` — the oracle may answer anything, so one passes to the
  limit.

This is the formula in which the **ω-rule** (a query node becomes a
supremum) and **ordinary computation** (a numeral is read exactly) coexist.
It is the right primitive, and everything else is read off it.

---

## Why `ε₀`, exactly

Here is the shape the argument *should* take — the picture the two
principles paint, and which a full proof must make rigorous (see the next
section for what is actually established). The height of a System T dialogue
tree ought to be bounded by a tower `ω↑↑(finite)`, with `ε₀` the limit of
these:

* **Type level 1** — ordinary loops over numbers (primitive recursion). A
  loop may run an oracle-many times; the answers are unbounded, so heights
  climb to a supremum — but, by linearity, only to `ω·(…)`, below `ω^ω`.
  *One* `ω`.
* **Each higher type level** lets one iterate a *functional* — a loop whose
  body builds loops — nesting the suprema: `ω`, `ω^ω`, `ω^{ω^ω}`, …, **one
  `ω` per level**.
* A term has a **finite** type level, hence a **finite** tower `ω↑↑ℓ`, well
  below `ε₀`.

`ε₀ = sup_ℓ ω↑↑ℓ` is reached by no single term but approached by the family.
That is exactly what it means for `ε₀` to be *the* ordinal of System T:
every term strictly below it, all of them together cofinal in it. The
type level is the tower height; the answer to "how deeply can a System T
functional interrogate its oracle?" is "`ω↑↑(its type level)` — and so, over
all of System T, as deep as `ε₀` but never that deep."

---

## What is proved, and what is open

**Proved and machine-checked** (`DialogueTreeHeight.*`, `--safe`, no
postulates) — the new, dialogue-specific content:

* the height function and its calculus: relabelling is height-free; the
  oracle adds one; grafting adds the grafted height (Lemmas L1–L3), in both
  a classical (ordinals) and a constructive (Brouwer-code) form;
* the operator `H`, its **composition law**, and the **law of iteration**
  above;
* the **Count Lemma**: counts are leaf *values*, so a bounded-magnitude
  count loops boundedly (no spurious supremum);
* the **conditional** recursor bound: *given* a bound on the orbit of
  heights `m ↦ h(f^m x)`, the iteration's height is bounded — the bound an
  explicit hypothesis, never a postulate.

These localise the conjecture's difficulty to a single statement:

> **Orbit lemma (open).** For every System T `f`, `sup_m h(f^m x) < ε₀`.

This is the heart, and it is genuinely open. It is equivalent to the
conjecture for the term "iterate `f` an oracle-many times", so it is not a
*smaller* lemma but the global theorem in local form. (The machine-checked
pieces handle each iteration *given* its orbit bound; assembling them into a
closed proof is the structural induction the open lemma controls — so the
honest statement is "conjecture and orbit lemma stand or fall together",
not "conjecture proved modulo a small gap".) The two principles
isolated above are the levers any proof must pull — **depth cannot see
itself** (hence the linearity that caps each level at one factor of `ω`),
and **counts are values** (hence the Count Lemma). Carrying them through a
Tait-style computability analysis, with the type level bounding the tower,
is the remaining ordinal-analytic work.

The problem is **Escardó's**, and remains **open**; the bound `ε₀` is the
**Gentzen–Tait** prediction; and the genuinely new idea — the lever that a
solution turns — is that the depth of the conversation is invisible to the
one having it.
