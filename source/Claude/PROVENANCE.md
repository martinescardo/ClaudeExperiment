# Provenance and attribution

This directory, `source/Claude/`, is the AI-authored code of **ClaudeExperiment**, an
experiment that **depends on** the
[TypeTopology](https://www.cs.bham.ac.uk/~mhe/TypeTopology/) Agda library but contains
none of it: the modules here import TypeTopology (`MLTT`, `UF`, `Ordinals`,
`EffectfulForcing.MFPSAndVariations`, …) via `depend: TypeTopology`, checked against
TypeTopology commit `bae60c78`. **Nothing here is, or ever was, committed to
TypeTopology itself.**

## Who did what

- **The Agda code** in `source/Claude/BrouwerOrdinals/` and
  `source/Claude/DialogueTreeHeight/`, the design notes (`dialogue-tree-height*.md`),
  the working notes (`notes/`), and the report (`report/`) were **authored by
  Claude** — across **Claude Fable 5** and **Claude Opus 4.8** (Anthropic) — over
  a series of sessions, **supervised by Martín Escardó**.

- **Much of the mathematics, not only its formalization, was Claude's**: the
  two-layer majorant/transformer framework, the overall strategy, the
  ordinal-arithmetic library, the hereditary transformer predicates, and the
  constructions and proofs. Escardó contributed the **conjecture** (that the
  dialogue-tree height of a System T term of type `(ι⇒ι)⇒ι` is `< ε₀`), the
  **supervision** throughout, and specific mathematical steers — notably pointing
  the work at the stratify-by-type-level strategy of the CSL 2011 paper he co-authored, an
  alternative Claude judged the more promising route, though it too ultimately
  failed.

- **An honest caveat on the split.** The work was developed untracked (no git
  history), and Claude's own memory of the sessions is compacted; so Claude cannot
  now reliably separate which ideas were its own and which were suggested by
  Escardó. Escardó, present throughout, declares that most of the work is Claude's.
  Exact per-file or per-model authorship is not reconstructed, and none is
  asserted.

## Status and honesty

**The conjecture is open.** This work does not settle it, nor a clean fragment
of it. Most of `DialogueTreeHeight/` consists of **abandoned explorations**, kept
deliberately as an honest record of the research process — see `report/` for a
first-person account, including a genuine error made and later caught.

## Verification

The trustworthy object here is the type-checker, not the author. Every module
type-checks under Agda with the flags in `ClaudeExperiment.agda-lib`
(`--without-K` etc.); the development is `--safe` with no postulates. From
`source/`:

```
agda Claude/BrouwerOrdinals/index.lagda
agda Claude/DialogueTreeHeight/Index.lagda
```

check the indexed tours; the standalone prototype modules are checked
individually.
