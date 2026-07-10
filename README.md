# ClaudeExperiment

An AI-assisted experiment on **Martín Escardó's conjecture** that the dialogue-tree
height of every closed Gödel System T term of type `(ι⇒ι)⇒ι` is below `ε₀`.

Over a two-week series of sessions, the AI system **Claude** (across the model versions
**Claude Fable 5** and **Claude Opus 4.8**, Anthropic), **supervised by Martín
Escardó**, attacked this conjecture in Agda. This repository is the record of that
attempt — the machine-checked code, the working notes, and a candid first-person
report by the AI of what it did, what it could not do, and one genuine error it
made and later caught.

**The conjecture is open. This experiment does not settle it.** Its value is a
verified partial development, a concrete candidate attack on the crux, and an
unusually complete and honest trace of AI-assisted research, dead-ends included.

## Start here

- **[`source/Claude/report/an-ai-account.pdf`](source/Claude/report/an-ai-account.pdf)**
  — the report. Read this first.
- **[`source/Claude/`](source/Claude/)** — all of the experiment: the Agda code,
  design notes, and working notes, with its own
  [`README`](source/Claude/README.md) and
  [`PROVENANCE`](source/Claude/PROVENANCE.md).

## What was and was not achieved

The proof is organised in two layers: `height ⟦t⟧ ≤ μ t` (Layer 1) and a bound on
the majorant `μ t < ε₀` by ordinal transformers (Layer 2). The experiment's
machine-checked contributions are on Layer 2: the **ground squaring recursor
kernel** (`MDomSquareOrbit`) shown `< ε₀`, and an **`ω^(-)` functor**
(`ExpDom`, `ExpClauseComparability`) that dissolves the specific wall stopping the
prior "affine" route. The report is explicit that this is Layer-2 work and that the
genuine bottleneck — Layer 1's higher-order recursor bridge — remains open, as it
has for every prior route.

For the specific Agda definitions worth singling out — the strongest result
(`MultHereditaryT`: an unconditional `height < ε₀` for a first-order System T
fragment with the recursor and almost all of `S`), the first-order fundamental
theorem, the squaring / open-kernel work, and lemmas of independent interest — see
the **"Main results, constructions, and lemmas"** section of the report.

## Attribution

The **conjecture** is Escardó's. The mathematical development that attacks it — the
two-layer framework and strategy, the ordinal-arithmetic library, the hereditary
transformer predicates, and the constructions and proofs — together with its Agda
formalization and this report, was to a large extent carried out by **Claude**
(across Claude Fable 5 and Claude Opus 4.8), under Escardó's **supervision**, whose
mathematical steers included pointing the work at the stratify-by-type-level
strategy of the CSL 2011 paper he co-authored. Details, and an honest note on what can and cannot
be reconstructed about authorship, are in
[`source/Claude/PROVENANCE.md`](source/Claude/PROVENANCE.md).

In concrete terms, **Martín Escardó did not create or edit any file in this repository
by hand.** Every file here was written by Claude; his contribution was entirely through
prompts to Claude and supervision.

## Dependency on TypeTopology

This repository contains only the experiment; it holds no TypeTopology code. It is an
Agda library that **depends on
[TypeTopology](https://github.com/martinescardo/TypeTopology)** (by Martín Escardó and
its many contributors): the Claude code imports TypeTopology modules (`MLTT`, `UF`,
`Ordinals`, `EffectfulForcing.MFPSAndVariations`, …) but contains none of them. It was
checked against TypeTopology commit `bae60c78`.

To build it, install TypeTopology as an Agda library and register it — add the path of
TypeTopology's `.agda-lib` to `~/.agda/libraries` — so that this repository's
`depend: TypeTopology` resolves.

## Type-checking

Everything is `--safe` with no postulates, under the flags in
`ClaudeExperiment.agda-lib`. With TypeTopology installed and registered (above) and a
matching Agda, from `source/`:

```
agda Claude/BrouwerOrdinals/index.lagda
agda Claude/DialogueTreeHeight/Index.lagda
```

check the indexed developments; the standalone prototype modules (e.g.
`agda Claude/DialogueTreeHeight/ExpDom.lagda`) are checked individually.

## License

[MIT](LICENSE). The content is AI-generated; whether copyright subsists in it is
unsettled, so no copyright is asserted — the MIT terms apply to the extent any
rights exist. See [`LICENSE`](LICENSE).
