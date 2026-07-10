# The dialogue-tree height problem: correct framing and attributions

> The canonical account **`dialogue-tree-height.md`** already incorporates
> these corrected attributions, elegantly and in narrative form. This note
> is the explicit correction record and the detailed who-proved-what.

*A correction of the record. Earlier notes in this directory leaned on
Howard's ordinal assignment as if it bounded dialogue-tree height. It does
not. This note states what each cited work actually proves, frames the
problem in the tradition it belongs to, and is honest about what is open.*

## 1. Correct attributions

* **Gödel (1958, Dialectica).** System T — the typed terms whose dialogue
  trees we study.
* **Gentzen (1936).** The proof-theoretic ordinal of Peano arithmetic is
  `ε₀`. This is *why* `ε₀` is the natural conjectured bound.
* **Tait; standard normalization theory.** System T is strongly normalizing,
  and its proof-theoretic / normalization strength is `ε₀`. The method is
  **computability (reducibility) predicates** with an ordinal assignment,
  and/or **infinitary terms** (the ω-rule). *This* is the tradition the
  dialogue-height problem belongs to.
* **Howard (1970), "Assignment of ordinals to terms for primitive recursive
  functionals of finite type."** Assigns ordinals `< ε₀` to System T terms
  bounding their **value / reduction complexity** (how the functionals
  grow, reduction lengths). **There are no dialogue trees in this work.** It
  legitimately bounds *magnitudes* (the numerical outputs) but says nothing
  about dialogue-tree *rank* — see §3.
* **Escardó (2013), "Continuity of Gödel's system T definable functionals
  via effectful forcing" (MFPS XXIX).** Introduces the **dialogue-tree
  interpretation** `B⟦_⟧` and the construction whose height we bound. **The
  conjecture — that these heights are bounded by `ε₀` — is Escardó's, and is
  the open problem here.**
* **Escardó & Oliva (2017), `Dialogue-to-Brouwer`.** Convert dialogue trees
  to **Brouwer trees**. This matters: a Brouwer tree *is* an ordinal
  notation, so dialogue-tree height is literally a (Brouwer) ordinal — the
  problem is intrinsically ordinal-theoretic, in these authors' own terms.

So: the *bound* `ε₀` is motivated by Gentzen/Tait; the *object* (dialogue
trees) and the *conjecture* are Escardó's; Howard is the **method** of
hereditary ordinal assignment but **not** a citable source for the height
bound.

## 2. The correct lens: the dialogue tree is an infinitary object

A dialogue tree `B ℕ = D ℕ ℕ ℕ` has leaves `η` and **ℕ-branching** query
nodes `β`. An ℕ-branching well-founded node is exactly an **ω-rule**
inference: "for every possible oracle answer `j ∈ ℕ`, here is the
continuation." So a dialogue tree is an **infinitary derivation / strategy**
in the sense of Schütte–Tait, and its height is the ordinal rank of that
infinitary object. Bounding it is therefore an instance of **ordinal
analysis of an infinitary calculus** — the Gentzen–Schütte–Tait programme —
*specialised to the dialogue strategy trees of System T*.

This is the framing I should have used from the start: not "Howard's term
ordinals," but "the rank of the ω-branching strategy tree", analysed by
computability/infinitary methods native to System T.

## 3. Why Howard's result does not transfer (the decisive point)

Howard bounds **values**; we need **rank**. These are independent for
dialogue trees:

> `x = iter' generic base (generic (η 0))` has **height `ω`** but its
> values stay `≤ b` under any oracle `≤ b`, i.e. **magnitude rank `0`**.

(`height ⊥ value`, established earlier in `…-howard-proof.md` §0.) A term
can nest `ω`-many adaptive queries while every answer, hence every value,
stays bounded. Howard's ordinals see the bounded values and say nothing
about the deep nesting. **This is exactly why borrowing Howard was wrong**,
and it is also the genuinely new structural fact (call it the
height–value independence) that any correct proof must exploit.

## 4. What is actually established, correctly attributed

Machine-checked in this directory (all `--safe`, no postulates):

* the height function and its calculus (Lemmas L1–L3) — *new,
  dialogue-specific*;
* the **operator** `H` with its composition law and the **recursor
  identity** `height(iter' f x n) = H(λk. height(fᵏ x)) n` — *new*;
* the **Count Lemma** (counts are leaf *values*, so a bounded-magnitude
  count iterates boundedly) — *new*;
* the **conditional** recursor bound: *given* an orbit bound, the iteration
  height is bounded — a proved implication, the orbit bound an explicit
  hypothesis.

On paper: the reduction of the conjecture to a single dialogue-native
lemma —

> **Orbit bound (the open lemma).** For System T `f`, `sup_k height(fᵏ x) <
> ε₀`.

— together with the two structural principles that should drive its proof:
**P1** height ⊥ value (⇒ the height-transform is *linear* in input height,
never exponential), and **P2** counts are magnitudes (⇒ the Count Lemma
applies). These are the new content; they are *what makes an ε₀ ordinal
analysis possible*, but they are not themselves that analysis.

## 5. Honest status, and the correct programme to finish it

The orbit bound is **not** Howard's theorem and **not** citable from it (or,
to my knowledge, from any extant work — it is specifically about Escardó's
dialogue strategy trees). It is equivalent to the conjecture for a related
term, so it is not a peelable sub-lemma but the heart of a **global**
argument.

The correct way to finish, in the right tradition:

1. **Computability/infinitary ordinal analysis, dialogue-native.** Set up a
   Tait-style computability predicate for the `B⟦_⟧` interpretation whose
   ordinal datum is the dialogue-tree rank, and handle the recursor by an
   inner induction up to `ω` (the ω-rule / orbit), with the type level
   bounding the nesting — yielding `ε₀ = sup_ℓ ω↑↑ℓ`. P1 caps each level's
   growth at `(·)·ω^{ρ}` (not exponentiation); P2 keeps counts honest.
2. This is a genuine ordinal-analysis development in the Gentzen–Tait–Schütte
   line, *for Escardó's dialogue interpretation*. It is not a corollary of
   Howard, Gentzen, or Tait individually — it is the same *kind* of theorem,
   to be proved for this specific object.

I have **not** carried out step 1, and I no longer attach anyone else's name
to its conclusion. The conjecture stands as **Escardó's open problem**, here
reduced (rigorously, with a machine-checked engine) to the dialogue-native
orbit bound, with the height–value independence (P1) the new lever. That is
the correct statement of where things stand.
