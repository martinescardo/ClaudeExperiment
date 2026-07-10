# `BrouwerOrdinals` — ordinal arithmetic on Brouwer codes

A small, **conjecture-free** library of ordinal arithmetic on Brouwer ordinal
codes — the toolkit on which the dialogue-tree-height development in
[`../DialogueTreeHeight/`](../DialogueTreeHeight/) stands. It imports only core
TypeTopology (`Ordinals.BrouwerCodes` plus basic `MLTT`/`UF`) and mentions nothing
about dialogue trees or System T, so it can be read on its own. Everything is
`--safe`, with no postulates.

## The setting

Brouwer ordinal codes `𝓑` (`Ordinals.BrouwerCodes`: zero `Z`, successor `S`, limit
`L : (ℕ → 𝓑) → 𝓑`) carry a *syntactic*, non-commutative arithmetic: order `≤` and
strict `<`, addition `⊕`, multiplication `⊗`, base-`ω` exponentiation `ω^_`, the
numerals `ι[_]`, the first limit `ω`, the tower `ω, ω^ω, ω^(ω^ω), …`, and
`ε₀ = L tower`. A recurring theme is **orbits**: iterating a majorant map and
bounding its supremum below `ε₀`.

## Module guide

**Foundations**
- `Order` — the syntactic order `≤` and addition `⊕`, with monotonicity.
- `Orbit` — multiplication `⊗`, the numerals `ι[_]`, `ω`, and the **additive
  fixed-increment orbit engine** (a fixed per-step increment costs one `⊗ ω`).
- `Epsilon0` — `ω^_`, the tower, `ε₀`, `<`; the monotonicity toolkit; the
  inflationary `a ≤ ω^a`; and the **`ε₀`-closure lemmas** (`S-<-ε₀`, `⊕-<-ε₀`,
  `ω^-<-ε₀`).
- `OmegaPoly` — natural sum via `ω`-polynomials; the multiplication closure
  `⊗-<-ε₀`; and the **exponent homomorphism `ω^⊗`** (`ω^x ⊗ ω^y = ω^(x ⊕ y)`).

**The affine layer** (majorants of shape `(b ⊕ c) ⊗ M`)
- `Affine` — `⊗` associativity / left-distributivity, and the doubling map with its
  orbit (`double-orbit-<-ε₀`).
- `AffineClosure` — small closure facts (`x ≤ x ⊗ M`, `Z < ε₀`, `ι[n] < ε₀`).
- `AffineOrbit` — the `ω`-affine orbit for an arbitrary sub-`ε₀` multiplier.
- `Affine2` — the two-argument jointly-affine class and the `S`-diagonal.

**The multiplicative layer**
- `MultAffine` — the limit-multiplier affine orbit (iterating `b ↦ (b ⊕ c) ⊗ M`):
  `ω`-positivity, the doubling-absorption `dbl-ω^`, and `crux`
  (`(Y ⊕ c) ⊗ M ≤ Y ⊗ M` when `c ≤ Y`).
- `MultOrbit` — the **multiplicative fixed-factor orbit engine**
  (`orbit-mult-sup-≤`, `pw-sup-≤`): a fixed factor `m < ε₀` per step stays `< ε₀`,
  past the `ω^ω` ceiling.
- `MultSquareOrbit` — the **squaring orbit** (`sq-orbit-<-ε₀`): iterating
  `b ↦ b ⊗ b` from a `< ε₀` start stays `< ε₀` (degree two, staying inside one
  `ω`-power).
- `MultDominated` — the **multiplier-dominated class** `MDom` (`ValidMult`,
  `MDom-orbit`, `MDom-∘`, `MDom2-diag`, `MDom-recursor-diag`): the ground recursor,
  composition, and `S`-diagonal closures.

**Auxiliary**
- `CNF`, `CNFAffine` — Cantor normal forms below `ε₀` with the natural (Hessenberg)
  sum, and affine maps with `ω`-power multipliers; a parallel representation, not on
  the final route.
- `MultBump` — the per-storey "bump" multiplier arithmetic of the (abandoned)
  Howard-tower route.

**`index`** — imports the library (the type-checking tour).

## Type-checking

With TypeTopology registered as an Agda library (see the
[top-level README](../../../README.md)), from the repository's `source/`:

```
agda Claude/BrouwerOrdinals/index.lagda
```

## Provenance

Part of the ClaudeExperiment; the code is Claude's, supervised by Martín Escardó.
See [`../PROVENANCE.md`](../PROVENANCE.md).
