# `source/Claude/` — the ClaudeExperiment code

This is the code of **ClaudeExperiment**, an AI-assisted experiment that **depends
on** the [TypeTopology](https://www.cs.bham.ac.uk/~mhe/TypeTopology/) library (but
contains none of it). It collects work done
by **Claude** (across **Claude Fable 5** and **Claude Opus 4.8**, Anthropic),
**supervised by Martín Escardó**, on his conjecture:

> The dialogue-tree height of every closed System T term of type `(ι⇒ι)⇒ι` is `< ε₀`.

**The conjecture is open.** This work does **not** settle it. Its value is a
machine-checked partial development, a candidate attack on the crux, and — unusually
— a complete and honest record of the attempt, dead-ends included. Read
[`report/an-ai-account.pdf`](report/an-ai-account.pdf) first: it is a first-person
account by the AI of what was achieved, what was not, and one real error made and
later caught.

For who-did-what, see [`PROVENANCE.md`](PROVENANCE.md). Nothing here is
committed to TypeTopology itself.

## Layout

- **`BrouwerOrdinals/`** (16 modules) — ordinal arithmetic on Brouwer codes: `⊕`,
  `⊗`, `ω^(-)`, `ε₀`, the orbit engines (`MultOrbit`, `MultSquareOrbit`), the
  multiplier-dominated class (`MultDominated`).
- **`DialogueTreeHeight/`** (69 modules + design notes `dialogue-tree-height*.md`) —
  the height development. A handful are the live line; the large majority are
  **documented abandoned explorations**, kept on purpose.
- **`report/`** — the experience report (`.tex` + `.pdf`).
- **`notes/`** — raw project working notes (`dialogue-tree-height-project.md`),
  included as-is as a process record; terse, informal, and containing reasoning
  that was later superseded.

## The live line (the parts that matter)

- Layer 1 (`DialogueTreeHeight/Majorant`): `height ⟦t⟧ ≤ μ t`, proved first-order.
- Layer 2 (transformer predicates): bounding the majorant by an ordinal `< ε₀`.
  The affine route is `AffTransformerPredicate`/`AffCombinators`/`IterFnProto`;
  the squaring frontier is `MDomSquareOrbit`, `ExpDom`, `ExpClauseComparability`.
- The last three are the final sessions' contribution: the ground squaring
  recursor kernel shown `< ε₀`, and the `ω^(-)`-functor mechanism that dissolves
  the affine route's linear-vs-squaring wall — machine-checked, but Layer-2 only,
  leaving the higher-order recursor bridge (Layer 1) as the open crux.

## Type-checking

Everything is `--safe`, no postulates, with the flags in
`ClaudeExperiment.agda-lib`. From `source/`:

```
agda Claude/BrouwerOrdinals/index.lagda
agda Claude/DialogueTreeHeight/Index.lagda
```

The standalone prototype modules (not all are in the tours) are checked
individually, e.g. `agda Claude/DialogueTreeHeight/ExpDom.lagda`.
