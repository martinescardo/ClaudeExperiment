# Function extensionality in this repository

This note audits **why function extensionality (funext) is used** in the
`BrouwerOrdinals/` folder, whether it can be avoided, and exactly where it is
crucial. It records a finding, not a change: nothing in the code was modified.

The audit of `DialogueTreeHeight/` (where the dependence is expected to be more
essential) is still to be done.

## Where funext is actually used

Every module in `source/Claude/BrouwerOrdinals/` is parameterized by
`fe : Fun-Ext`, but almost all of that is *threading* — passing `fe` on to
imported submodules. Genuine uses of extensionality are exactly **7 sites**, all
the identical idiom

```agda
… (L f) = ap L (dfunext fe (λ n → IH (f n)))
```

in the limit (`L`) case of a `＝`-valued induction:

| Site | Lemma | Statement |
|------|-------|-----------|
| `Orbit.lagda:67` | `⊕-assoc` | `(a ⊕ b) ⊕ c ＝ a ⊕ (b ⊕ c)` |
| `Affine.lagda:88` | `⊗-left-distrib` | `c ⊗ (x ⊕ y) ＝ (c ⊗ x) ⊕ (c ⊗ y)` |
| `Affine.lagda:199` | `⊗-assoc` | `(a ⊗ b) ⊗ c ＝ a ⊗ (b ⊗ c)` |
| `AffineClosure.lagda:52` | `SZ-⊗` | `(S Z) ⊗ y ＝ y`  (left unit, `1 ⊗ y = y`) |
| `Epsilon0.lagda:68` | `Z-left-unit` | `Z ⊕ a ＝ a` |
| `Epsilon0.lagda:191` | `ω^-ι1` | `ω^ ι[ 1 ] ＝ ω` |
| `OmegaPoly.lagda:216` | `ω^⊗` | `ω^ a ⊗ ω^ b ＝ ω^ (a ⊕ b)` |

The last, `ω^⊗`, is the exponent homomorphism `ω^x ⊗ ω^y = ω^(x⊕y)` that the
report highlights as the ω^(-) homomorphism.

Everywhere else, `fe` is only threaded into imports. In particular the
foundational module `Order.lagda` takes `fe` but **never uses it** in its body.

## Why it is needed — the exact mechanism

Brouwer codes have the constructor

```agda
L : (ℕ → 𝓑) → 𝓑
```

and every operation acts pointwise on it:

```agda
a ⊕ L f = L (λ n → a ⊕ f n)
a ⊗ L f = L (λ n → a ⊗ f n)
```

To prove an **equation** whose argument is `L f`, both sides compute to `L g₁`
and `L g₂`, and the induction hypothesis gives `g₁ n ＝ g₂ n` for every `n`.
Concluding `L g₁ ＝ L g₂` (then `ap L`) requires `g₁ ＝ g₂` — i.e. promoting a
*pointwise* equality of the two sequences to an equality of the **functions**.
That promotion is precisely what `dfunext` does. Only the `ℕ → 𝓑` instance is
ever used (universe-monomorphic, `𝓤₀`).

## Can it be avoided?

**Yes in principle — and the code already shows the escape route.** Compare, in
`Orbit.lagda`, the same limit case for two statements:

```agda
⊕-mono-left … (L f) = ≤-L-mono (λ n → ⊕-mono-left p (f n))      -- no funext
⊕-assoc   a b (L f) = ap L (dfunext fe (λ n → ⊕-assoc a b (f n))) -- funext
```

The difference is entirely `≤` vs `＝`. The order `_≤_` (in `Order.lagda`) is an
*inductive relation* whose limit rules consume pointwise families directly:

```agda
≤-ℓ : {a : 𝓑} {f : ℕ → 𝓑} (n : ℕ) → a ≤ f n → a ≤ L f
≤-L : {f : ℕ → 𝓑} {b : 𝓑} → ((n : ℕ) → f n ≤ b) → L f ≤ b
```

so limit cases of `≤` close without funext. Propositional equality `＝` has no
such pointwise limit rule; that is the whole source of the dependency.

The funext requirement therefore comes **solely from choosing to state these
seven laws as propositional equalities on codes containing `L`.** Two ways out:

1. **Principled route.** Replace those `＝`-laws with an inductively-defined
   equivalence `_≈_` (a limit rule taking pointwise `f n ≈ g n`), or with
   two-sided `≤`. Then the `L` cases close by the pointwise constructor,
   funext-free. Cost: the downstream code currently `transport`s along these
   equalities; one would thread `≈` (and its congruences) through those
   rewrites instead. Non-trivial but mechanical.

2. **Keep `＝`, keep funext.** It is a very mild instance, and it genuinely
   *cannot* be discharged — even `ℕ`-funext is not provable in `--without-K`
   MLTT — so if these are wanted as honest equalities at `L`, funext is
   unavoidable.

## Caveat about "avoiding it in the repository"

Making `BrouwerOrdinals/` funext-free would **not** make the repository
funext-free: the TypeTopology effectful-forcing / dialogue machinery it depends
on, and the `DialogueTreeHeight/` layer on top, also assume `Fun-Ext`. Within
this folder, though, the picture is clean — funext is used in exactly the seven
limit-case equalities above, and is avoidable only by not using `＝` at the `L`
constructor.
