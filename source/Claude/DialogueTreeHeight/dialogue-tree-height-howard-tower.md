# The Howard tower: design note (2026-07-03)

Status note for the `DialogueTreeHeight` development, following module 45
(`MultHereditaryG`). Records the design analysis behind the decision to
follow Howard's insights, and the precise specification of the next
development. Nothing here is proved beyond what the modules prove; the
conjecture (height of dialogue trees of System T terms `< ε₀`) remains
**open**.

## 1. Where the line of development stands

* Design F (`MultHereditaryF`, module 37) dissolved the type-structural
  wall: every argument carries its own globally-valid weight-transformer,
  and ground-`S` and the recursor close in one predicate.
* The affine zone calculus (modules 38–44) discharged the recursor's
  orbit-closure on the inner-affine class and produced fundamental theorems
  for successively larger fragments (`T⁺`, `T₂`, `T₃`), which turn out to be
  **pairwise incomparable**: finer data buys more `S`-diagonals but demands
  data that coarser fragments simply never owed.
* Design G (`MultHereditaryG`, module 45) added Howard-style *data maps*
  (`𝔻 ι` = a good bound function, `𝔻 (σ⇒τ) = 𝔻 σ → 𝔻 τ`). The structural
  half of the tower is then free — `K` and the full `S` close for **all**
  types in one line each — and the residual concentrates in the recursor:
  data maps must be *tracked* (dominated by an inner-affine
  bound-transformer), and the level-1 tracked calculus is the module-39
  affine calculus, transferred by reuse.

## 2. The regress, precisely

A fundamental theorem over Design G must carry `Tracked` hereditarily: a
tracking relation `𝕂` on data. The `S`-diagonal *of data maps* at a
function-typed middle then demands tracking **of tracking** — because a
term's data map has the same combinator structure as the term itself, each
storey's diagonal needs the next storey. This is not an artifact: any
*compositional bound relation* whose ground data is quantitative
(sub-`ε₀` bounds with an orbit-closed multiplier class) reproduces itself
one level up. Fixing any finite number of storeys reproduces the
`T⁺`/`T₂`/`T₃` fragment lattice, shifted.

## 3. What "trust Howard" means here

Howard's 1970 assignment gives each term of T an ordinal `< ε₀` via
**vectors of ordinals indexed by type level**, with application a *fixed*
arithmetic operation on vectors. Two readings for our height problem:

**(a) The operational reading.** Bound the dialogue-tree height by the
length of a symbolic head-reduction of `t · generic`, and cite/formalize
ordinal decrease under reduction. This is mathematically the classical
route, but it requires infrastructure the repository does not have: an
operational semantics for (combinatory) T with an oracle constant, an
adequacy theorem relating it to the dialogue (denotational) semantics, and
Howard's decrease lemma — and the recursor-unfolding step consumes the
*value* of the count, so the count/magnitude component (the `TwoComponent`
(A)/(B) split recorded earlier) reappears inside the operational route as
well. A large, separate development.

**(b) The structural reading — the one this development adopts.** Howard's
vectors have length equal to the **type level**. Read as a logical
relation, this says: the tracking tower of §2 is not an infinite regress
but an **ℕ-indexed hierarchy whose depth is bounded by the type level of
the term at hand**. A term `t : σ` only ever needs storeys up to (roughly)
the maximal type level occurring in `t`; the combinators are polymorphic in
the storey index. The self-similarity of §2 is then exactly Howard's
observation that each type level contributes one layer of ordinal data —
one `ω`-exponent of room — and `ε₀ = sup_ℓ ω↑↑ℓ` emerges as the join over
type levels, which is the shape the conjecture always had ("one `ω` per
type level", the canonical note's tower).

Concretely, the next development is:

* `Trk : ℕ → (σ : type) → 𝔻 σ → 𝓤₀` by recursion on the storey index `n`
  (and inside it on `σ`): storey `0` is trivial; storey `n+1` at an arrow
  carries (i) maps preserving storey-`(n+1)` tracking, and (ii) an affine
  zone component in the style of the `JAff` calculus, whose *own*
  cross-diagonal obligations refer to storey `n`.
* At level 1 this is `MultHereditaryG.Tracked`, whose calculus (composition,
  orbit) is already proven by reuse of `MultHereditaryFAff`.
* The zone arithmetic of storey `n+1` is the module-39/43 affine calculus
  read on storey-`n` bound data; the engine lemmas (`absorb`,
  `Sg-diag`, orbit) are expected to transfer the same way `Tracked-∘`
  reused `AffBounded-∘`.
* Fundamental theorem shape: `∀ (t : T₁ σ) → Σ n , tracked-to-storey n`,
  with `n` bounded by the syntactic level of `t` — a *level-polymorphic*
  statement, so no fragment restrictions on `S`/`K` instances at all;
  `T₁`-completeness (full combinatory System T with the ground recursor)
  is the target.
* The height connection is unchanged: `Majorant.height-≤-μ` plus ground
  extraction.

A possible simplification to investigate first: storeys `≥ 2` appear
structurally identical (all are affine-data maps over affine data), so the
hierarchy may collapse to *two* genuinely distinct storeys plus an indexed
repetition — in which case the fundamental theorem needs only a single new
predicate rather than an ℕ-family.

## 4. Honest scope

* Nothing in §3(b) is proved yet beyond storey 1 (module 45).
* The known hard points to watch: the storey-`(n+1)` `S`-diagonal with
  function-typed middle (this is where storey `n` is consumed — the design
  must make the consumption *arithmetic*, as in `JAff-Sg-diag`, not another
  map); and the recursor's interaction with storeys `≥ 2` (nested `Iter`
  raises the multiplier one `ω`-exponent per nesting — the storey data must
  have room, which is what the per-level `ω`-exponent provides).
* Even with `T₁` complete, the full conjecture (recursor at higher types)
  remains open — that is where the genuinely super-linear transformers
  live (`MultSquareOrbit` bounds their orbits individually; no closed class
  containing them is known).
