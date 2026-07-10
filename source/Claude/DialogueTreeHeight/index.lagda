\begin{code}

{-# OPTIONS --safe --without-K #-}

module Claude.DialogueTreeHeight.index where

import Claude.DialogueTreeHeight.Classical
import Claude.DialogueTreeHeight.Constructive
import Claude.DialogueTreeHeight.Count
import Claude.DialogueTreeHeight.Operator
import Claude.DialogueTreeHeight.Conditional
import Claude.DialogueTreeHeight.Orbit
import Claude.DialogueTreeHeight.Magnitude
import Claude.DialogueTreeHeight.FirstOrder
import Claude.DialogueTreeHeight.Majorant
import Claude.DialogueTreeHeight.Hereditary
import Claude.DialogueTreeHeight.TwoComponent
import Claude.DialogueTreeHeight.Bridge
import Claude.DialogueTreeHeight.PolyAffine
import Claude.DialogueTreeHeight.PolyHereditary
import Claude.DialogueTreeHeight.PolyTransformer
import Claude.DialogueTreeHeight.Nested
import Claude.DialogueTreeHeight.Applicative
import Claude.DialogueTreeHeight.CNFTransformer
import Claude.DialogueTreeHeight.MultApplicative
import Claude.DialogueTreeHeight.MultApplicativeT
import Claude.DialogueTreeHeight.MultHereditary
import Claude.DialogueTreeHeight.MultHereditaryT
import Claude.DialogueTreeHeight.MultHereditaryB
import Claude.DialogueTreeHeight.MultHereditaryE
import Claude.DialogueTreeHeight.MultHereditaryF
import Claude.DialogueTreeHeight.MultHereditaryFLin
import Claude.DialogueTreeHeight.MultHereditaryFAff
import Claude.DialogueTreeHeight.MultHereditaryFT
import Claude.DialogueTreeHeight.MultHereditaryFAff2
import Claude.DialogueTreeHeight.MultHereditaryFJT
import Claude.DialogueTreeHeight.MultHereditaryFAffN
import Claude.DialogueTreeHeight.MultHereditaryFNT
import Claude.DialogueTreeHeight.MultHereditaryG
import Claude.DialogueTreeHeight.MultHereditaryG2
import Claude.DialogueTreeHeight.MultHereditaryH
import Claude.DialogueTreeHeight.MultHereditaryH2
import Claude.DialogueTreeHeight.MultHereditaryH3
import Claude.DialogueTreeHeight.MultHereditaryH4
import Claude.DialogueTreeHeight.MultHereditaryH5
import Claude.DialogueTreeHeight.MultHereditaryH6
import Claude.DialogueTreeHeight.MultHereditaryHT
import Claude.DialogueTreeHeight.MultHereditaryH7
import Claude.DialogueTreeHeight.MultHereditaryH8
import Claude.DialogueTreeHeight.MultHereditaryH9
import Claude.DialogueTreeHeight.MultHereditaryHTK
import Claude.DialogueTreeHeight.MultHereditaryH10
import Claude.DialogueTreeHeight.MultHereditaryH11
import Claude.DialogueTreeHeight.MultHereditaryH12
import Claude.DialogueTreeHeight.MultHereditaryH13
import Claude.DialogueTreeHeight.MultHereditaryH14
import Claude.DialogueTreeHeight.MultHereditaryH15
import Claude.DialogueTreeHeight.MultHereditaryH16
import Claude.DialogueTreeHeight.MultHereditaryH17

\end{code}

Dialogue-tree heights: a guided tour of the verified core.

This indexes the machine-checked part of the development described, in
prose, in `EffectfulForcing/DialogueTreeHeight/dialogue-tree-height.md` (the canonical
account). The question: the dialogue tree of a System T term `t : (ι⇒ι)⇒ι`
records its adaptive interrogation of the oracle; its height is an ordinal;
Escardó conjectured it is `< ε₀`. The modules below verify the new,
dialogue-specific mathematics that reduces the conjecture to a single open
"orbit lemma"; everything here is `--safe` with no postulates.

The pure Brouwer-ordinal arithmetic developed along the way — the order and
addition, multiplication and `ω`, the orbit engines, `ε₀`, `ω`-polynomials,
Cantor normal forms, affine maps, valid multipliers, the bump operator — has
been factored out into the standalone library `BrouwerOrdinals` (its own
`Claude.BrouwerOrdinals.index`), which does not depend on dialogue trees or System T.
Tour entries below that name a `Claude.BrouwerOrdinals.*` module describe a component
of that library, kept here in chronological context.

The reading order, matching the sections of `dialogue-tree-height.md`:

(1) `DialogueTreeHeight.Classical` — "The picture" and "depth cannot see itself",
    classical form. Height as a genuine ordinal (`Ordinal 𝓤₀`), and the
    height calculus L1–L3: relabelling is height-free (`height-relabel`),
    the oracle adds one (`height-generic`), grafting adds the grafted height
    (`height-kleisli-extension`). Uses excluded middle, because the
    successor on ordinals is not monotone without it.

(2) `DialogueTreeHeight.Constructive` — the same L1–L3, constructively, with
    heights as Brouwer ordinal codes and their syntactic order, for which
    the successor is monotone by construction. No excluded middle.

(3) `DialogueTreeHeight.Count` — "counts are values": the magnitude predicate
    `values-≤` and the Count Lemma `height-kleisli-extension-≤`, by which a
    bounded count iterates boundedly (no spurious supremum). The oracle is
    the unique source of unbounded counts.

(4) `DialogueTreeHeight.Operator` — "The law of iteration". The value-
    sensitive height operator `H`, its composition law
    `H-kleisli-extension`, and the recursor identity `height-iter'`:
    `height (iterate f, n times, from x) = H (λ m → height (fᵐ x)) n`,
    in which a numeral count is read exactly and a query node becomes a
    supremum. Plus the combinator algebra (`H-η`, `H-generic`,
    `H-B-functor-succ`).

(5) `DialogueTreeHeight.Conditional` — the reduction made honest: *given* a
    bound on the orbit of heights `m ↦ height (fᵐ x)`, the iteration's
    height is bounded (`height-iter-≤-orbit-bound`). The orbit bound is an
    explicit hypothesis — the open "orbit lemma", the dialogue-side instance
    of Howard's `|System T| = ε₀` (the height is the *rank* of the
    oracle-interaction, which Howard's ordinal dominates; see the corrected
    note in `Conditional` and the (A)+(B) split in `TwoComponent`). It is
    Escardó's open problem, but now localized to bridge (B), with (A) a
    Howard citation.

(6) `DialogueTreeHeight.Orbit` — "depth cannot bootstrap", made into an
    engine. The conditional bound (5) wants a *uniform* orbit bound; this
    module *produces* one from a strictly **local** datum: if each step of
    the orbit raises the height by at most a *fixed* code `c` —
    independently of how deep the orbit already is — then the orbit
    supremum is `≤ height x ⊕ (c ⊗ ω)` (`orbit-sup-≤`), and hence the
    oracle-driven iteration has height `≤ (height x ⊕ c ⊗ ω) ⊕ height n`
    (`height-iter-from-step`). This is the precise linearity the conjecture
    turns on: a depth-independent per-step increment costs only one extra
    factor of `ω`, never an exponential in the depth. The increment `c` is
    an explicit hypothesis; for first-order `f` it is `ω^ω`, and pinning
    that down for closed terms (so `c, height x, height n < ε₀`) is the
    remaining typed induction this engine feeds.

(7) `DialogueTreeHeight.Magnitude` — the **magnitude** half, the component
    the height-only majorant was blind to. Values are bounded *relative to a
    bound on the oracle*: `mag-≤ V x` says `dialogue x α ≤ V b` whenever the
    oracle `α` is bounded by `b`. The propagation laws (`mag-η`, `mag-succ'`,
    `mag-generic`, `mag-kleisli`) make precise that the oracle is the sole
    source of magnitude — `mag-generic` shows `generic` resets the magnitude
    to `λ b → b` regardless of its input — and `mag-kleisli` realises
    **Lemma R1**, the count bound: the iteration count `dialogue n α` is
    itself `≤ V b`. This is the value-side input the orbit engine (6) needs
    to fix the per-step increment `c` for a first-order term.

(8) `Claude.BrouwerOrdinals.Epsilon0` — the ε₀ arithmetic on Brouwer codes that
    turns the engine's output code into a genuine `< ε₀` statement. Adds
    base-`ω` exponentiation `ω^_`, the tower `tower`, `ε₀ = L tower`, and the
    strict order. Proves the monotonicity toolkit (`⊕`, `⊗`, `ω^_`), the
    inflationary law `a ≤ ω^ a`, the strict climb `ω < ω^ ω` and
    `tower n < ε₀`, and the key absorption the first-order orbit needs:
    `ω^ω ⊗ ω < ε₀` (`ω^ω⊗ω-<-ε₀`) — so the engine's first-order increment
    `c = ω^ω` keeps the iteration height `< ε₀`. Also the additive `< ε₀`
    closure `⊕-<-ε₀`. Sub-development (I) of the frontier note is complete.

(9) `DialogueTreeHeight.FirstOrder` — the capstone assembly: the first-order
    **recursor** height bound `height (iter' f x n) < ε₀`
    (`height-iter-<-ε₀`), given the first-order per-step increment `ω^ω` and
    that the subterm heights `height x, height n` are `< ε₀`. Pure assembly
    of (6) the engine and (8) the ε₀ arithmetic. The three hypotheses are
    the honest interface to the one remaining piece — the structural term
    induction (sub-development (II)) that discharges them — so this module is
    the verified target that induction lands on. The full conjecture
    (higher-type iteration, the climb to `ε₀` itself) remains open.

(10) `DialogueTreeHeight.Majorant` — sub-development (II): the **first-order
     fundamental theorem**, by structural induction on the term. A
     height-indexed logical relation (`Maj ι = 𝓑`, `R ι x a := height x ≤ a`,
     hereditary) majorizes every combinator (`R-Zero/Succ/Ω/K/S`), with the
     ground recursor `R-Iter` closed via (5)'s `height-iter-≤-orbit-bound`
     and the orbit supremum `μ-Iter φ a ν = (sup_k φᵏ a) ⊕ ν`. The
     first-order syntax is `T₁` (`Iter` only at `ι`); the theorem
     `fundamental` gives `height ⟦t⟧ ≤ μ t`, and `dialogue-height-≤-μ` the
     dialogue-tree height bound for first-order `t : (ι⇒ι)⇒ι`. A height-only
     majorant suffices here (magnitude is a higher-type concern). What
     remains for the first-order `< ε₀` theorem: that `μ t < ε₀`, the
     affine-class closure — all its ε₀-arithmetic ingredients are in (8).

(11) `Claude.BrouwerOrdinals.Affine` — toward `μ t < ε₀`. The majorant's orbit
     suprema `sup_k φᵏ a` are bounded via affine reasoning. Key results:
     left distributivity `⊗-left-distrib`; `⊗ω-<-ε₀` (one `ω` factor stays
     `< ε₀`); the **multiplicative orbit** `double-orbit-<-ε₀` (iterating
     `b ↦ b ⊕ b` gives `sup ≤ a ⊗ ω < ε₀` — the case once feared to escape);
     the **fold lemma** `affine-fold` (`x ⊗ ι[p+1] ⊕ d ≤ (x ⊕ d) ⊗ ι[p+1]`)
     which makes affine maps compose with the constant kept inside,
     sidestepping the failure of right distributivity (no Hessenberg natural
     sum needed); and — the payoff — the **general affine-orbit bound**
     `affine-orbit-<-ε₀`: for affine `φ b ≤ (b ⊕ d) ⊗ ι[p+1]` with `d < ε₀`,
     `sup_k φᵏ a ≤ (a ⊕ d ⊗ ω) ⊗ ω < ε₀`. That is exactly what `μ-Iter`
     needs.

(12) `Claude.BrouwerOrdinals.AffineClosure` — the closure properties of the
     affine class `Aff φ := (φ b ≤ (b ⊕ d) ⊗ ι[m])` (positive numeral
     multiplier `ι[m]`, constant kept inside). The `ι⇒ι` majorants that arise
     are affine: `Aff-id`, `Aff-S` (successor), `const-Aff` (`K`),
     `const-left-Aff` (`λν. C ⊕ ν`), `Aff-Iter-partial` (the recursor's
     partial application, via the orbit bound); and `Aff` is closed under
     composition `Aff-∘` and pointwise sum `Aff-⊕` — the steps that let
     `K, S` build affine functions with no right distributivity. (`Aff-app`
     applies an affine majorant to a sub-`ε₀` input.) These are the building
     blocks of the hereditary closure that would give `μ t < ε₀`. The
     remaining piece is the hereditary predicate itself: ground arguments
     need a *uniform joint* affine bound, while function arguments need a
     *data-dependent transformer* (the bound on the result depends on the
     argument's affine data — e.g. `μ-Iter`'s orbit sup depends on its
     iterated function); reconciling these is exactly Howard's hereditarily-
     majorizable functionals, and is the substantial step still open.

(13) `DialogueTreeHeight.Hereditary` — the hereditary predicate `𝔅`, which
     resolves the joint/transformer tension: `φ` is good iff, for every
     assignment of good majorants to its *function* arguments (∀, transformer
     — `FunArgs`/`plug`), the result as a function of its *ground* arguments
     is *jointly affine* relative to a common upper bound `s` (`JB`/
     `JointAff`). The common bound `s` makes the joint bound symmetric, so
     combining uses associativity not commutativity. Proved: the mutual
     definition is well-formed; ground extraction `𝔅 ι a ⟺ a < ε₀`; the
     argument-shift `JB-shift`; **application closure** `𝔅-app`; and the base
     combinators `𝔅-Zero/Succ/Ω`. All `--safe`, no postulates.

     What this construction reveals (the definitive ceiling): the finite-`ι[m]`
     affine class caps at `≈ ω^ω`. Full first-order `ε₀` needs `ω^c`
     multipliers — because nested iteration *from a varying start* (e.g.
     `Iter (λx. Iter G x M) X N`, first-order) makes the iterated function
     `ω`-affine, and the orbit of an `ω`-affine function climbs the tower.
     But `affine-fold` provably *fails* for limit multipliers (`(L g) ⊕ d`
     cannot be absorbed when `g`'s base is a limit), so the constant-inside
     trick does not extend to `ω`. So full `ε₀` requires the `ω^c`-multiplier
     affine class closed under the Hessenberg **natural sum** (Part II's
     actual route) — a separate substantial development. The affine approach
     here is a clean sub-`ε₀` (`≈ ω^ω`) fragment; the tower to `ε₀` is
     fast-growing-hierarchy territory.

(14) `Claude.BrouwerOrdinals.OmegaPoly` — the natural sum, built. Since
     `affine-fold` is provably false for `ω` (`ω·ω + 1 = ω²+1 > ω² =
     (ω+1)·ω`), the Hessenberg **natural (commutative) sum** is genuinely
     required. For the first-order fragment (`< ω^ω`) the ordinals are
     **ω-polynomials** `c₀ + ω·c₁ + ⋯` with ℕ coefficients, on which the
     natural sum `⊞` is just coefficient-wise addition (manifestly
     commutative). With the Horner denotation `⟦ c ∷ cs ⟧ = (ω ⊗ ⟦cs⟧) ⊕
     ι[c]` into Brouwer codes, the key lemma `poly-key`/`poly-key'`:
     `⟦p⟧ ⊕ ⟦q⟧ ≤ ⟦p ⊞ q⟧` (ordinary sum ≤ natural sum, *both orders*) — the
     commutative upper bound the non-commutative `⊕` could not give, via the
     absorption of lower-degree terms by higher (`absorb`). And the route now
     *concludes* `< ε₀`: `poly-<-ε₀` (every ω-polynomial is `< ε₀`) and
     `⊞-<-ε₀` (the natural sum is `< ε₀`), via the exponent homomorphism
     `ω^⊗ : ω^a ⊗ ω^b ＝ ω^{a⊕b}` and `ω·tower n ≤ tower (n+1)`. And the
     **right-distributing scalar multiplication** the affine closure needs
     (which `affine-fold` could *not* provide for `ω`): "multiply by `ω^k`" is
     `shift k` (prepend `k` zeros), with `shift-⊞ : shift k (p ⊞ q) = shift k
     p ⊞ shift k q` (distributes over the natural sum), `shift-shift`
     (composes, exponents add), and `shift-pow : ⟦ shift k p ⟧ ＝ ω^ι[k] ⊗
     ⟦ p ⟧` (the bridge to the Brouwer-code height bounds). So the *arithmetic*
     foundation for the first-order `< ε₀` bound is now complete: commutative
     sum with a `< ε₀` conclusion, and a distributing/composing `ω^k` scalar.
     All `--safe`, no postulates. What remains is the *hereditary structure*
     (Howard's majorizability over function types) — independent of this
     arithmetic.

(15) `DialogueTreeHeight.TwoComponent` — the Howard route, structured.
     Taking `|System T| = ε₀` seriously: the dialogue height is the *ordinal
     rank* of a term's oracle-interaction, and Howard's ordinal dominates such
     ranks (the "height ⊥ value" worry conflated value with rank — corrected
     in `Conditional`). So the right majorant carries *both* components: a
     ground tree is majorized by a pair `(a , V)` — height bound `a` and
     magnitude function `V` — with `R₂ ι x (a,V) := height x ≤ a × mag-≤ V x`,
     hereditary. Proved: the structural combinators `R₂-Zero/Succ/Ω/K/S` and
     application in two-component form (magnitude rows = the `mag-*` lemmas,
     `Ω`'s being the oracle reset). The recursor `R₂-Iter-ground` is isolated
     as **(A) + (B)**: its magnitude is the machine-checked `mag-kleisli`
     (Lemma R1, the count `≤ V b`) with the orbit-magnitude data as input —
     this is the Howard component **(A)**, citable; and its height is the
     machine-checked conditional bound *given* the orbit-height bound — the
     dialogue-native residual **(B)**. So the whole conjecture is localized,
     in machine-checked form, to (B), with (A) a Howard citation and the rest
     proved. All `--safe`, no postulates.

(16) `DialogueTreeHeight.Bridge` — attacking (B). The residual orbit bound is
     `(B1)` per-step increment `≤ ω^{eₖ}` + `(A)` `eₖ ≤ β < ε₀` [Howard] +
     the engine; the engine handles `(B2)`, so the heart is `(B1)`, whose core
     is the **tower-step** `iter-tower-step`: iterating a function of
     height-increment `ω^e` raises the exponent to `e+1` — one `ω` per nesting
     level (`ω^ι[e] ⊗ ω = ω^ι[e+1]`), the source of `ω↑↑ℓ`. With the base
     `Ω-increment` (oracle = `ω^0`). The open kernel is precisely that a
     functional's increment *is* `ω^magnitude` carried hereditarily — the
     dialogue-specific content; the tower-step is its engine, the magnitude
     bound its (A). The numeral-exponent step caps at the first-order ceiling
     `ω^ω`; the engine is exponent-agnostic, so `iter-tower-step-code`
     generalizes it verbatim to a Brouwer-code exponent `e : 𝓑` (raising the
     exponent to `S e`), and `iter-tower-step-<-ε₀` closes the ε₀ accounting for
     any `e < ε₀` (via `Epsilon0.S-<-ε₀, ω^-<-ε₀, ⊕-<-ε₀`). This is the
     *higher-type* tower mechanism (`ω↑↑ℓ` with the exponent an ordinal `tower ℓ`,
     not a numeral) as a machine-checked theorem — still conditional on (B1).

(17) `DialogueTreeHeight.PolyAffine` — affine composition, unblocked. The
     affine class `f b ≤ (b ⊕ d) ⊗ ω^k` did *not* compose (needs the fold
     lemma, false for `ω`). Carrying the bound as a *polynomial* fixes it:
     `PAff k d f := ∀ pb, b ≤ ⟦pb⟧ → f b ≤ ⟦ (shift k pb) ⊞ d ⟧` (input scaled
     by `ω^k` via `shift`, plus constant polynomial `d`, with the *commutative*
     natural sum `⊞`). Then `PAff-∘` proves composition closes —
     `PAff k d ∘ PAff k′ e = PAff (k+k′) (shift k e ⊞ d)` — by pure polynomial
     algebra (`shift-⊞`, `shift-shift`, `⊞`-assoc), exactly the `K`/`S`
     building block the non-commutative `⊕`/`⊗` could not provide. With the
     base cases `PAff-id`, `PAff-S`, and the payoff `PAff-<-ε₀` (poly-affine
     maps poly-bounded inputs to outputs `< ε₀`). And the bridge to the
     conjecture: `PAff-orbit` — the *orbit* `j ↦ fʲ b` of a poly-affine map,
     from a poly-bounded start, is `< ε₀` (each iterate stays polynomially
     bounded; the supremum is a family of ω-polynomials, `< ε₀` by
     `OmegaPoly.poly-family-<-ε₀`, which rests on the strict degree bound
     `poly-str : S⟦p⟧ ≤ ω^ι[length p]`, giving `⟦p⟧ ≤ ω^ω`). So the
     first-order orbit lemma is discharged for every poly-affine height
     transform, with `PAff-∘` supplying combinator closure. Down to the *real*
     dialogue height: `transform-orbit` — if a tree transform `f` has its
     height controlled by a poly-affine `f̂` (`height (f y) ≤ f̂ (height y)`, the
     machine-checked "depth cannot see itself" for `f`), then the orbit of
     heights `k ↦ height (fᵏ x)` is `< ε₀`. So the conjecture's orbit lemma is
     reduced *exactly* to poly-affineness of the height transform. Unconditional
     instance `generic-orbit`: iterating the oracle has orbit height `< ε₀`.
     Base leaves `PAff-id`, `PAff-S`, `PAff-const`, `PAff-add`. And the
     *additive* tree-transform layer: `Additive f c := ∀ y, height (f y) ≤
     height y ⊕ ⟦c⟧`, which composes with increments adding by the commutative
     natural sum (`add-∘ : Additive f cf → Additive g cg → Additive (f ∘ g)
     (cg ⊞ cf)`) and has orbit `< ε₀` (`add-orbit`, via `transform-orbit`). So
     *every finite composite of constant-increment (oracle/relabel) operations*
     has orbit of heights `< ε₀`, unconditionally. Crucially that orbit stays
     *poly-bounded* — `add-orbit-poly : … ≤ ω^ι[max (deg start) (deg incr)]` —
     since an additive step keeps the polynomial *degree* fixed (only
     coefficients grow). This is the recursive enabler: a *nested* recursor's
     orbit is again a polynomial bound, feeding the next level — the mechanism
     of the first-order tower `ω, ω², …, < ω^ω`. The toolkit is *complete* at
     the majorant level: `poly-map-orbit` (abstract additive map) and
     `poly-map-orbit-mult` — an iterated majorant that *multiplies* (multiplicity
     `k`, via `S`) still has a poly-bounded orbit, because `nmul k` scales
     *coefficients* not *degree*. So the recursor orbit is polynomial for
     *every* first-order iterated majorant. All `--safe`, no postulates.

(18) `DialogueTreeHeight.PolyHereditary` — the hereditary predicate rebuilt
     over ω-polynomials with the commutative natural sum `⊞` and an explicit
     *multiplicity* `k`. The finite-`ι[m]` predicate (`Hereditary`) could not
     reorder/duplicate ground arguments (non-commutative `⊕`/`⊗`) nor carry the
     multiplicity a combinator like `S` needs (it uses its ground argument
     twice). Here the joint bound is `JBp ι a ps k d := a ≤ ⟦ nmul k ps ⊞ d ⟧`:
     relative to a common polynomial bound `ps` on the ground arguments, the
     result is `k` natural-summed copies of `ps` plus a constant polynomial `d`.
     `⊞` is commutative (`poly-key` in either order) so arguments reorder/
     duplicate freely, and `nmul k` scales *coefficients* not *degree*, matching
     `PolyAffine.poly-map-orbit-mult`. Proved: the mutual `FunArgs`/`plug`/`𝔅p`
     is well-formed; ground extraction `𝔅p ι a ⟺ a poly-bounded` (`𝔅pι-poly-
     bound`, `poly-bounded-to-𝔅pι`) and hence `𝔅p ι a → a < ε₀`; the poly
     algebra it needs (`⊞-exch`, `nmul-⊞`, `nmul-[]`); the argument-shift
     `JBp-shift` (absorb a dropped common-bound part into the constant with
     multiplicity, via the commutative `⊞`); **application closure** `𝔅p-app`;
     and the base combinators `𝔅p-Zero/Succ/Ω`. All `--safe`, no postulates.

     Honest ceiling (as for `Hereditary`): the polynomial multiplier caps the
     fragment at `ω^ω`, so ground extraction is poly-boundedness, *not* `< ε₀`
     in full — the tower to `ε₀` needs `ω^c` (CNF) multipliers. What this
     establishes is the hereditary fundamental theorem *for the maximal
     polynomial fragment*. Combinator closure: `𝔅p-K` (via the weakening lemma
     `𝔅p-weaken` — an ignored argument of any type preserves goodness) and
     `𝔅p-S-higher` (the `S` diagonal when the shared argument has function
     type — closes by three `𝔅p-app`s, reusing the same `FunArgs` entry). What
     precisely does *not* close, and why (both for the *same* reason — the joint
     bound `nmul k ps ⊞ d` is affine in the common bound `ps`): the *ground*
     diagonal of `S` (`ρ = ι`, `σ` a function type — the argument `γ x` is
     function-valued and varies with the ground `x`, but `𝔅p` fixes function
     arguments *before* `x`), and `𝔅p-Iter` (the recursor's orbit is
     `ω^ι[m] = ⟦shift m (1∷[])⟧`, degree `m+1`, exceeding any fixed
     `nmul K ps ⊞ D` — it *raises* the ω-degree, the first-order tower hitting
     the affine ceiling). Both pin the remaining work to one precise
     generalisation: `JBp` bounding by `⟦ T ps ⟧` for a polynomial *transformer*
     `T : Poly → Poly`, with `FunArgs` carrying transformer-valued goodness —
     Howard's hereditarily-majorizable functionals with a genuine transformer
     component.

(19) `Claude.BrouwerOrdinals.MultOrbit` — the **multiplicative** orbit engine, past
     the `ω^ω` ceiling. `Orbit` is additive (a fixed *increment* `c`, one factor
     of `ω`); the higher-type climb is *multiplicative* (a fixed *factor* `m`
     per step, `a (k+1) ≤ a k ⊗ m`, with `m` a sub-`ε₀` ordinal — the height of
     the iterated functional's body, not a numeral). The ω-polynomial route
     could only handle finite / `ω^k` factors, hence its `ω^ω` cap; here the
     factor is *arbitrary* below `ε₀`. Proved: `pw m k ≤ ω^(m ⊗ ι[k])` (each
     power dominated by an `ω`-power, via the inflationary `m ≤ ω^ m` and the
     exponent homomorphism `ω^⊗`), so the power supremum is `L (pw m) ≤ ω^(m ⊗ ω)`
     (definitional: `ω^(m ⊗ ω) = L (λ k → ω^(m ⊗ ι[k]))`) and `< ε₀` by the new
     multiplicative closure `⊗-<-ε₀`. The engine `orbit-mult-sup-≤`:
     `L a ≤ a 0 ⊗ L (pw m)`, and `orbit-mult-<-ε₀`: `L a < ε₀` for `m, a 0 < ε₀`.
     This is the multiplicative counterpart of `Orbit.orbit-sup-≤`, reaching any
     factor below `ε₀` — the engine for *one* type-level of the tower. (Open
     kernel, as ever: that a functional's per-step factor genuinely is such an
     `m`, carried hereditarily. The engine no longer imposes a ceiling on it.)
     Supporting arithmetic (in `OmegaPoly`): `⊗-<-ε₀` (`ε₀` closed under ordinal
     `⊗`, via `tower-sq : tower n ⊗ tower n ≤ tower (succ n)`) and (in `Epsilon0`)
     `S-<-ε₀`, `ω^-<-ε₀` (`ε₀` closed under successor and `ω`-exponentiation).

(20) `DialogueTreeHeight.PolyTransformer` — the hereditary predicate over a
     polynomial **transformer** `T : Poly → Poly`, generalising the *affine*
     ground bound of `PolyHereditary` (`nmul k ps ⊞ d`) to an arbitrary
     `⟦ T ps ⟧`. Two payoffs. (i) The combinator closures get *simpler*: an
     abstract transformer composes by ordinary function composition, so
     application reindexes by `T ↦ T ∘ (_⊞ dG)` (`JBpT-app-reindex`) with no
     `nmul`/`⊞` bookkeeping; `𝔅pT-app`, `𝔅pT-K`, `𝔅pT-weaken`, `𝔅pT-S-higher`
     and the base `𝔅pT-Zero/Succ/Ω` all carry over, and ground extraction
     `𝔅pTι-to-<ε₀` still holds (every `T []` is a polynomial, hence `< ε₀`).
     (ii) The recursor is now *expressible*: `𝔅pT-Iter-affine` closes `Iter`
     for an affine inner function `g` (`g b ≤ ⟦ nmul kg pb ⊞ dg ⟧`), producing
     the **degree-raising** transformer `T ps = shift (max (length ps)
     (length dg) + 1) [1]` (denoting `ω^ι[m+1]`) — the bound
     `PolyHereditary.JBp` provably could not hold, since its affine shape keeps
     the degree fixed. The orbit is discharged by `PolyAffine.poly-map-orbit-mult`
     plus `ω^-double` (`ω^ι[m] ⊕ ω^ι[m] ≤ ω^ι[m] ⊗ ω = ω^ι[m+1]`). The one
     piece the abstract transformer *drops* is the affine shape (`kg , dg`) that
     `poly-map-orbit-mult` consumes, so the fully hereditary `Iter` combinator
     (which sees `g` only through `𝔅pT (ι ⇒ ι) g`) still needs an affine-tracking
     transformer class — the honest open interface, now isolated to exactly that
     shape information.

(21) `DialogueTreeHeight.Nested` — attacking **(B1)** directly: the per-step
     increment of a *nested* recursor is *grafting*, hence proven, not assumed.
     The bridge (B) splits into (B1) "increment `≤ ω^e`" and (B2) "orbit stays
     `< ε₀`" (done). Everywhere so far (B1) is a hypothesis (`Orbit`, `Bridge`,
     `Conditional` take the increment as a function argument). Here it is
     *discharged* for the shape that drives the tower — a body
     `f y = kleisli-extension g y` (grafting a family `g`; for a nested recursor
     `g = iter h z`, the inner orbit). New ingredient: the **left-increment
     orbit engine** (companion to `Orbit`'s right-increment one — `⊕` is
     non-commutative, so they differ), `b⊗-succ-swap` + `orbit-left-≤/sup/uniform`:
     a fixed *left* increment `b` per step forces `L a ≤ (b ⊗ ω) ⊕ a₀`, one
     factor of `ω`. The increment `b = sup_k height (g k)` is read off the
     grafting lemma `height-kleisli-extension` — the machine-checked "depth
     cannot see itself" (grafts chosen without seeing `y`'s depth). Payoff:
     `kleisli-orbit-uniform`, `height-nested-iter`, and `height-nested-iter-<-ε₀`
     — with graft heights `≤ ω^e` the nested iteration is `< ε₀` (using
     `b ⊗ ω = ω^e ⊗ ω = ω^{e+1}` definitionally). So **one recursor nesting
     costs exactly one `ω`-power, proven**. And it **composes**:
     `nested-orbit-uniform-<-ε₀` generalises the graft bound to any `c < ε₀` and
     shows the uniform orbit bound `(c ⊗ ω) ⊕ height x` is again `< ε₀`, so a
     grafting body's orbit can serve as the graft family of an outer nesting —
     the class closes under the nested-recursor step (`height-nested-iter-<-ε₀-gen`).
     These lemmas apply to a genuine term: `⟦ Iter (λ m → Iter H Z m) X N ⟧`
     interprets (via `MFPS-XXIX.iter'`) to exactly `kleisli-extension
     (iter (λ y → kleisli-extension (iter ĥ ẑ) y) x) n`, the graft family being
     the inner orbit. Residual: the *syntactic bridge* — that a System T body's
     dialogue interpretation has this grafting-body shape hereditarily, grounding
     `c` in the magnitude (Howard (A)) via the Count Lemma. (B1) is now reduced
     from an assumed per-step increment to that structural step.

(22) `DialogueTreeHeight.Applicative` — the **first UNCONDITIONAL `height < ε₀`**
     theorem, for a recursor-closed fragment. Everything above bounds a height by
     `ε₀` only *conditionally* (on an orbit bound, a per-step increment, a graft
     bound, or a majorant's affine shape). Here `height-<-ε₀ : (x : Gnd) →
     height ⟦ x ⟧G < ε₀` holds with **no hypotheses**. The fragment is the
     **single-argument first-order** sublanguage (two mutually recursive sorts
     `Gnd`/`Fun`): every function has type `ι ⇒ ι` — the functions are `Ω`,
     `Succ`, partial recursors `Iter f x`, **composition** `f ∘ g`, and
     **constants** `λ _ → x` (the ground `K`); ground terms are `Zero` and
     applications. What is excluded is exactly the `S` *diagonal*
     `λ a → φ a (γ a)`, which would force a multi-argument joint bound. So the
     persistent wall never arises: `Aff-μF`/`good-μG` (every function majorant
     affine, every ground majorant `< ε₀`) is one clean mutual induction — the
     recursor discharged by `AffineClosure.Aff-Iter-partial`, composition by
     `Aff-∘`, constants by `const-Aff`, application by `Aff-app`; correctness
     `R-G`/`R-F` (height `≤` majorant) is the logical relation restricted to the
     fragment, its recursor case closed by `Conditional.height-iter-≤-orbit-bound`
     on the orbit sup. `height-recursor-<-ε₀`: the recursor driven by an arbitrary
     ground count (e.g. an oracle read `appG ΩF zeroG`, unbounded magnitude, so
     the orbit sup is genuinely taken) is `< ε₀`. Exponents are finite here (so
     really `< ω^ω`); the `S` diagonal and the tower to `ε₀` proper are the open
     hereditary closure — this is the maximal fragment the single-argument affine
     class alone closes.

(23) `Claude.BrouwerOrdinals.Affine2` — the **two-argument jointly-affine class**,
     first assault on the `S` wall. `Aff2 φ` bounds a two-argument `φ` relative
     to a *common* upper bound `s` on both arguments: `φ a b ≤ (s ⊕ d) ⊗ ι[m]`
     for `a , b ≤ s` (symmetric, so reordering uses only `⊕`-associativity, à la
     `Hereditary`). The crux `Aff2-diag`: **a jointly-affine `φ` diagonalised
     against an affine `γ` is single-argument affine** — `Aff2 φ → Aff γ →
     Aff (λ a → φ a (γ a))` — exactly the ground `S`-combinator closure, by the
     same `affine-fold-num` technique as `Aff-∘` with common bound
     `s = (a ⊕ e) ⊗ ι[n]` (dominating `a` and `γ a`). Plus the projections
     `Aff2-π₁/π₂`, the lifts `Aff-to-Aff2-left/right` (a single-argument affine
     as a two-argument one ignoring the other slot), and `Aff2-app`. Scope: the
     multiplier is a *finite* `ι[m]`; a recursor `Iter f` as the two-argument
     function is jointly affine only with an `ω`-multiplier (orbit sup
     `(a ⊕ d ⊗ ω) ⊗ ω`), which the `⊗`-fold cannot reach. Crucially, `ω`-affine
     functions are **not closed under composition** (two compose to `ω²`) — that
     non-closure *is* the type-level tower `ω↑↑ℓ`, the open conjecture, not a
     patchable gap. What *is* available is the **pointwise** `ω`-level: `Good2 φ`
     (`< ε₀` output on `< ε₀` inputs, no uniform multiplier hence no composition
     demand) holds for the recursor `Good2-Iter` (via `Affine.affine-orbit-<-ε₀`),
     and the diagonal against it is `< ε₀` pointwise (`Good2-diag`,
     `recursor-diag-<-ε₀`: the `S`-diagonal `λ a → Iter f a (γ a)` is `< ε₀` at
     every `< ε₀` argument). So the recursor `S`-diagonal is bounded whenever
     *applied*, but not in a class closed under further composition/iteration —
     the honest ceiling of the `⊗`-affine route, exactly at the tower boundary.

(24) `Claude.BrouwerOrdinals.CNF` — **Cantor normal forms below `ε₀`**, the `ε₀`
     generalisation of `OmegaPoly`'s `ω`-polynomials. A datatype `CNF`
     (`𝟎 | ω⟨_⟩+_`, a sum of `ω`-powers whose exponents are themselves CNFs, so
     all of `< ε₀` is reachable), the denotation `⟦_⟧ : CNF → 𝓑`, and the
     headline `cnf-<-ε₀ : ⟦ c ⟧ < ε₀` (by `ε₀`-closure under `ω^` and `⊕`). Plus
     `ωpow`, and the ordinary (non-commutative) sum `_⊕c_` with `⊕c-⟦⟧` (it
     denotes `⊕`). The point is the **natural sum**, whose ordinal heart is
     proved here: `absorb-ω-succ : A ≤ B → ω^A ⊕ ω^(S B) ≤ ω^(S B)` (a smaller
     `ω`-power is absorbed on the left of a larger), via `⊕⊗-succ` (the
     `Nested.b⊗-succ-swap` shape) and `ωB⊕ωBω` (the limit `ω^B ⊗ ω` swallows one
     more `ω^B`); hence `ωpow-swap-succ` (two comparable `ω`-powers commute up to
     `≤`). Strengthened to whole tails: `principal-succ` (`ω^(S B)` absorbs
     anything below a finite multiple of `ω^B`, by left distributivity) and
     `absorb-tail` (a CNF all of whose exponents are `≤ B`, `AllExpLeq`, is
     absorbed on the left of `ω^(S B)` — via `tail-≤`, folding its `len p` powers
     up by `⊕⊗-succ`). This is *exactly* the merge step: moving a larger leading
     power to the front past the tail below it. **Finding:** the merge realising
     the *exact* commutative `⊞` must *compare* exponents, and unlike `OmegaPoly`
     (exponents were list positions, freely comparable as `ℕ`) the nested CNF
     exponents have **no free constructive total order** (Brouwer-code `≤` is
     undecidable at limits). **Resolution — sidestep the sort.** What the sorted
     natural sum was *for* is keeping the leading exponent fixed while
     coefficients add, and `tail-≤` delivers exactly that from a **common
     exponent bound**: `common-bound : AllExpLeq m p → AllExpLeq m q →
     ⟦p⟧ ⊕ ⟦q⟧ ≤ ω^m ⊗ ι[len p + len q]` — a bound *symmetric* in `p , q` (it
     depends only on their sizes), so it dominates the sum in either order, and
     `common-bound-<-ε₀` gives `< ε₀`. So the natural-sum-quality commutative
     bound (leading exponent fixed, coefficients add) is obtained **without a
     decidable comparison**, by supplying the common exponent bound the affine
     structure already provides. This is the arithmetic that lets composition of
     `ω`-power-affine maps close past `ω^ω` toward `ε₀`. The **converse bridge**
     `<ε₀-to-cnf`: *every* `< ε₀` code is CNF-bounded (`a < ε₀` gives `a ≤ tower n`,
     and `tower n` is a CNF, `tower-cnf`) — so the whole Brouwer-code `< ε₀` world,
     including the `Aff` class's constants, can be re-read with CNF bounds.

(25) `Claude.BrouwerOrdinals.CNFAffine` — **the affine class that composes past
     `ω^ω`**, the payoff of the CNF arithmetic. `PolyAffine`'s `PAff` scaled the
     input by `ω^k` for `k` a *numeral* (cap `ω^ω`); here the scalar is `ω^⟦m⟧`
     for `m` an arbitrary CNF, so *any* multiplier `< ε₀` is reachable. `CAff f`:
     `f b ≤ ⟦ ωscale m p ⊕c d ⟧` for every CNF `p` with `b ≤ ⟦p⟧`, where `ωscale
     m` multiplies by `ω^⟦m⟧` (adds `m` to every exponent; `ωscale-⟦⟧` proves it
     denotes `ω^⟦m⟧ ⊗ _`, the CNF `shift-pow`) and `⊕c` is ordinary CNF sum. The
     crux **`CAff-∘`**: `CAff` is closed under composition — the `⊗`-fold
     `(x ⊗ M ⊕ d) ≤ (x ⊕ d) ⊗ M` that `Aff` needed is *false* for limit `M` (the
     tower wall), but here the bound is a CNF and composition closes by pure CNF
     algebra: `ωscale-⊕c` (scaling distributes over `⊕c`), `ωscale-ωscale`
     (scalings compose, exponents adding by `⊕c`), `⊕c-assoc` — **no fold, and no
     commutative merge** (composition is single-threaded; the merge is only for
     the multi-argument joint bound). Base maps `CAff-id`, `CAff-add`, and
     `CAff-ωpow` (multiply-by-`ω^α` is `CAff` for *every* `α < ε₀` — past the
     `ω^ω` ceiling); payoff `CAff-<-ε₀`. So affine maps with multipliers anywhere
     below `ε₀` compose and stay `< ε₀` — the closure the type-level tower needs,
     which the finite `⊗`-fold could not give. The **iteration** side too:
     `left-mult-orbit-<-ε₀` — a left-multiplicative orbit (`a(k+1) ≤ ω^m ⊗ a k`,
     the side `ωscale` produces, counterpart of `MultOrbit`'s right engine) has
     supremum `ω^(m ⊗ ω) ⊗ a₀`, `< ε₀` for `m < ε₀` (the `k`-th iterate
     `≤ ω^(m ⊗ ι[k]) ⊗ a₀`, exponent accumulating via `ω^⊗` and `CNF.⊕⊗-succ`).
     Hence `CAff-ωpow-orbit-<-ε₀`: iterating multiply-by-`ω^α` from a sub-`ε₀`
     start stays `< ε₀` — the multiplicative tower step at any multiplier below
     `ε₀`. So both composition and iteration of `ω`-power-affine maps are closed
     to `ε₀`; the arithmetic ceiling is fully gone. Finally the **additive class,
     closed under composition AND iteration** — the shape the recursor both
     consumes and produces. `Add f` (`f b ≤ b ⊕ ⟦c⟧`, fixed CNF constant) with
     `Add-id`, `Add-∘` (constants add via `⊕c`), and — the crux — `Add-orbit`:
     *iterating an additive map is additive again*, the constant growing from `c`
     to `scaleω c` (orbit `≤ a ⊕ ⟦c⟧⊗ω`, then `scaleω`), still a CNF `< ε₀`
     (`Add-<-ε₀`). `scaleω` (`⟦c⟧⊗ω ≤ ⟦scaleω c⟧`, via `topexps` + `tail-≤`) is
     the enabling arithmetic. So a nested recursor with additive body **stays
     additive**: the tower's consume-vs-produce shape-mismatch is resolved for
     the additive class, and the single-threaded fragment is fully closed at
     `ε₀`. The remaining wall is now *purely* the multi-argument (`K`/`S`)
     duplication, which pure additivity cannot express. Toward it: `nmulc k p`
     (`k` copies of `p`, `⟦nmulc k p⟧ ≤ ⟦p⟧ ⊗ ι[k]` via `nmulc-≤`; `nmulc-dup`
     bounds `⟦p⟧ ⊕ ⟦p⟧`) — the finite multiplier for a repeated argument.
     Caveat found in the proving: `nmulc` sits on the *non-commutative* `⊕c`, so
     it does **not** distribute (does not itself compose); the *composable*
     symmetric duplication bound is `CNF.common-bound` (common exponent bound, no
     sort). So the joint-bound reordering is `common-bound`'s job, `nmulc` giving
     the finite multiplicity `ι[k]`. Finally, the **coherent function-type
     shape**: `Add±` (two-sided additive, `f b ≤ (⟦α⟧ ⊕ b) ⊕ ⟦β⟧`) contains the
     recursor's *partial* application `λ ν → orbit ⊕ ν` (left constant,
     `Add±-const-left`, which right-additive `Add` misses since `⊕` is not
     commutative) and every right-additive map (`Add-to-Add±`), and is closed
     under **both** composition (`Add±-∘`, constants accumulating on their sides)
     **and iteration** (`Add±-orbit`: the orbit is `Add±` again, both constants
     grown by `scaleω` via `⊕⊗-succ` on each side). So one class holds recursor
     partials, oracle/relabel maps, their composites and their orbits, all
     `< ε₀` — the `ι ⇒ ι` shape a hereditary predicate can carry through `Iter`,
     resolving the consume-vs-produce mismatch for two-sided-additive bodies.
     Assembled: `Add±-app` (apply to a CNF-bounded argument → CNF-bounded result)
     and — the hereditary `Iter` step `CNFTransformer`'s abstract transformer
     could not take — `Add±-Iter-partial`: `μ-Iter g x = λ ν → orbit(x) ⊕ ν` is
     `Add±` (the orbit is CNF-bounded at the fixed start `x` by `Add±-orbit`, fed
     to `Add±-const-left`). So *given `Add±` shape for the body*, the recursor
     closes hereditarily — the shape-loss wall is gone. The remaining structural
     residual is only the multi-argument `S`-diagonal (which needs a finite
     multiplier `Add±` lacks). Toward *that*: the finite-multiplier `Aff` class
     (which `Affine2.Aff2-diag` shows handles the diagonal) has an orbit that
     escaped to an `ω`-multiplier — but that is no longer a ceiling.
     `Aff-orbit-cnf`: the orbit of an `Aff` (duplicating) body is **CNF-bounded**
     — from `Affine.affine-orbit-≤` (`L (λ k → iter φ a k) ≤ (a ⊕ d ⊗ ω) ⊗ ω`),
     the `< ε₀` constant `d` becomes a CNF (`CNF.<ε₀-to-cnf`) and the two `⊗ ω`
     become `scaleω`, landing the whole orbit in one CNF. So a *duplicating* body,
     iterated, stays `< ε₀` with an explicit CNF bound — the `Aff` (duplication)
     and CNF-orbit (iteration) sides meeting, which is what the `S`-diagonal needs.
     The two halves are then **joined in one statement**: `Sdiag-orbit-cnf`
     composes `Affine2.Aff2-diag` (a jointly-affine `φ` diagonalised against an
     affine `γ` is a duplicating `Aff` body) with `Aff-orbit-cnf`, so *iterating a
     ground `S`-diagonal* — the one operation the additive/`CAff`/`Add±` classes
     could not express — stays CNF-bounded (`Sdiag-orbit-<-ε₀`: `< ε₀`). And the
     **feed-forward** `Sdiag-nest2`: the CNF-bounded orbit of one duplicating
     recursor is exactly the start-hypothesis the same lemma consumes, so
     finitely-nested ground `S`-diagonal recursors stay `< ε₀` — the tower for the
     duplicating case, one bounded exponentiation per level, finitely many below
     `ε₀`.

(26) `DialogueTreeHeight.CNFTransformer` — the **`ε₀` lift of `PolyTransformer`**,
     the hereditary predicate over a *CNF* transformer `T : CNF → CNF`. Reruns
     `PolyTransformer`'s development (`JBpT`/`JointAffpT`/mutual
     `FunArgs`/`plug`/`𝔅pT`, `JBpT-app-reindex`, `𝔅pT-app`/`-Zero`/`-Succ`/`-Ω`/
     `-weaken`/`-K`/`-S-higher`) with `Poly ↦ CNF` and the poly natural sum `⊞`
     replaced by the ordinary CNF sum `⊕c` — which only needs to be *increasing*
     on each side (`cnf-≤-⊕c-left/right`), not commutative, since the abstract
     transformer composes by plain function composition. The gain: **ground
     extraction `𝔅pTι-to-<ε₀` now lands at `ε₀`** (every `T 𝟎` is a CNF, hence
     `< ε₀`), where `PolyTransformer` capped at `ω^ω`. So `K`, `S`-higher,
     application and the base combinators close the hereditary predicate *at
     `ε₀`*. **And the recursor, additive case:** `𝔅pT-Iter-additive` closes
     `Iter` for an additive inner `g` (`g b ≤ b ⊕ ⟦c⟧`) — the `Orbit` engine
     bounds the orbit by `a ⊕ (⟦c⟧ ⊗ ω)`, and `CNFAffine.scaleω` (`⟦c⟧ ⊗ ω ≤
     ⟦scaleω c⟧`, built from `CNF.tail-≤` + `topexps`) turns it into the CNF
     transformer `T p = (p ⊕c scaleω c) ⊕c p`. Where
     `PolyTransformer.𝔅pT-Iter-affine` produced a degree-raising *poly*
     transformer (cap `ω^ω`), this produces a genuine *CNF* one, so the recursor
     output reaches `ε₀`. Residual (unchanged from `PolyTransformer`): the
     *ground* `S`-diagonal, and the *fully hereditary* `Iter` (needs `𝔅pT (ι⇒ι)
     g` to expose additive/affine shape, not an abstract transformer). The `ω^ω`
     ceiling is gone throughout, replaced by `ε₀`.

(28) `Claude.BrouwerOrdinals.MultAffine` — **iterating a *limit*-multiplier affine
     body — the first crack in the multiplier wall.** The finite-`Aff` class
     iterates only because `Affine.affine-fold` (`b ⊗ ι[m] ⊕ d ≤ (b ⊕ d) ⊗ ι[m]`)
     lets the constant escape the multiplier; that fold is provably *false for a
     limit multiplier* (`1 ⊗ ω ⊕ 1 = ω+1 > ω = 2 ⊗ ω`), which is exactly why the
     start-varying recursor (`ω`-affine majorant `(a ⊕ d ⊗ ω) ⊗ ω`) "could not
     iterate" — the tower. This module iterates the body `mbody c b = (b ⊕ c) ⊗ M`
     **without** `affine-fold`, for any positive `M` that *absorbs doubling*
     (`ι[2] ⊗ M ≤ M` — every principal limit: `ω`, `ω ⊗ 2`, `ω^ω`, …): the crux
     `c ≤ Y → (Y ⊕ c) ⊗ M ≤ Y ⊗ M` pushes `⊗ M` inward (`Y ⊕ c ≤ Y ⊕ Y =
     Y ⊗ ι[2]`, then absorb), so the orbit telescopes against the powers `Mᵏ`
     (`MultOrbit.pw`): `iter (mbody c) a k ≤ (a ⊕ c) ⊗ Mᵏ`, sup `(a ⊕ c) ⊗
     ω^(M ⊗ ω) < ε₀` (`mult-affine-orbit-<-ε₀`; `M = ω` instance
     `mult-ω-orbit-<-ε₀`). **Connected to the recursor:** `affine-orbit-≤` bounds
     the start-varying recursor majorant `σ a = L (λ j → iter φ a j)` by exactly
     `mbody[ω] (d ⊗ ω) a`, so `recursor-start-orbit-<-ε₀` — *iterating* `σ`
     (nesting the recursor on its own running start, the canonical single-nesting
     tower term) — is `< ε₀`, via `iter-dominate` (that body is monotone) onto the
     `M = ω` orbit. So a limit-multiplier iteration is bounded, past the
     finite-`Aff` ceiling. **And the nesting *composes*:** the orbit of an
     `M`-body is bounded by an `mbody` again at the *raised* multiplier
     `M′ = ω^(M ⊗ ω)` (`mbody-orbit-≤`: `L (pw M) ≤ ω^(M ⊗ ω)`), and `M′` is
     *again* positive, doubling-absorbing (`dbl-ω^`: `ι[2] ⊗ ω^(X ⊗ ω) ≤
     ω^(X ⊗ ω)`) and `< ε₀`. So the limit-multiplier class is **closed under
     taking orbits**, each recursor-nesting level raising the multiplier
     `M ↦ ω^(M ⊗ ω)` — the explicit multiplier tower `Mult` (`ω`, `ω^(ω⊗ω)`, …),
     every level a valid multiplier (`Mult-pos`/`-dbl`/`-<-ε₀`), so
     `mult-tower-orbit-<-ε₀` bounds a limit-multiplier orbit at *any* finite
     level, and `nest2-<-ε₀` witnesses the composed two-level nesting `< ε₀`.
     This is the type-level tower `ω ↑↑ ℓ` as an inexhaustible-below-`ε₀`
     sequence of multipliers, one `ω`-exponentiation per level, in pure
     Brouwer-code arithmetic — the tower's *arithmetic* obstacle removed. Honest
     scope: what remains open is the *structural* step (that a general
     first-order term's majorant **is** such a finite `mbody`-nesting, threaded
     hereditarily) and the full diagonal's lower-order `⊕ γ a` glue — not the
     arithmetic of composing/iterating limit multipliers, which is now closed.

(29) `Claude.BrouwerOrdinals.MultDominated` — **the hereditary recursor closure the
     transformer predicates could not take.** Packages `MultAffine`'s
     orbit-stable shape as a predicate `MDom φ = Σ M , ValidMult M × Σ c , c < ε₀
     × (∀ b → φ b ≤ (b ⊕ c) ⊗ M)`, a `ValidMult` being a positive,
     doubling-absorbing, `< ε₀` multiplier — closed under `⊗` (`validMult-⊗`, for
     composition) and the orbit-raise `M ↦ ω^(M ⊗ ω)` (`validMult-orbit`, for
     iteration). Leaves: `MDom-additive` (identity, successor, oracle-relabel, at
     multiplier `ω`). The payoff **`MDom-orbit`**: the start-varying recursor
     majorant `λ a → L (λ k → iter φ a k)` of an `MDom` body is `MDom` *again*, at
     the raised multiplier `ω^(M ⊗ ω)` and the same constant — a two-line
     consequence of `iter-dominate` + `mbody-orbit-≤`, because the shape survives
     its own orbit. This is *exactly* the case `Hereditary`/`PolyHereditary`/
     `PolyTransformer`/`CNFTransformer` all hit as a wall (their `ι ⇒ ι`
     predicate either dropped the iterable shape or was not orbit-closed). With
     `MDom-app` (application to a `< ε₀` argument) and `MDom-orbit-<-ε₀`, the
     recursor is closed for the multiplier-dominated shape. **And the rest closes
     too, without right-sub-distributivity.** *Composition* `MDom-∘`: naively
     `φ (ψ b) ≤ ((b ⊕ c_ψ) ⊗ M_ψ ⊕ c_φ) ⊗ M_φ`, and pulling `c_φ` out would need
     the false `affine-fold`; instead **enlarge the inner constant** to
     `c_ψ ⊕ c_φ`, so `c_φ ≤ (b ⊕ (c_ψ ⊕ c_φ)) ⊗ M_ψ` and `MultAffine.crux`
     absorbs it — composite at multiplier `M_ψ ⊗ M_φ`, no output constant.
     *Ground `S`-diagonal* `MDom2-diag` (via the jointly-dominated two-argument
     class `MDom2`, common-bound form): the same enlarge-then-`crux` trick with
     common bound `s = (x ⊕ c*) ⊗ M_G` closes `λ x → F x (G x)`. And the
     *partial recursor is jointly dominated* (`MDom2-Iter`: `F a ν =
     L (λ k → iter φ a k) ⊕ ν ≤ (s ⊕ c) ⊗ (M′ ⊗ ι[2])` under a common `s`), so
     the **recursor `S`-diagonal** `λ x → Iter φ x (G x)` — the canonical
     tower-driving term — is `MDom` (`MDom-recursor-diag`). So the
     multiplier-dominated class is closed under **composition, iteration (the
     recursor orbit), and duplication (the `S`-diagonal)** simultaneously, all
     `< ε₀` — the three operations that, jointly, define the tower, with the
     per-function multiplier climbing `M ↦ ω^(M ⊗ ω)` (or `⊗`) but every finite
     composite staying below `ε₀`. **This is the arithmetic/majorant-level heart
     of the first-order theorem, complete** — every closure that blocked the
     prior hereditary predicates is discharged. Honest scope: this is the
     *majorant* class (functions `𝓑 → 𝓑`); what remains is the *structural*
     assembly — the type-indexed hereditary predicate over all first-order types
     (function arguments, `K`/`S` at higher types, the `FunArgs`/`plug`
     machinery) and its connection to actual dialogue height (`height ⟦t⟧ ≤`
     majorant) — now with every arithmetic closure it needs available. The
     conjecture is *not* proved; the remaining work is type-structural plumbing,
     not an arithmetic wall.

(30) `DialogueTreeHeight.MultApplicative` — **the `MDom` closures, cashed in on
     real dialogue trees: an unconditional `height < ε₀` for a fragment that
     *includes* the recursor `S`-diagonal.** This is the `MDom` analogue of
     `Applicative` (22): the same skeleton — concrete two-sort syntax
     (`Gnd`/`Fun`), interpretation into the dialogue model, height majorants,
     and a logical relation `R-G`/`R-F` — but with `Aff` replaced by `MDom` and
     a new constructor `iterDiagF φ G` for the recursor `S`-diagonal
     `λ x → Iter φ x (G x)` (iterate `φ` from the bound variable `x` for `G x`
     steps), which `Applicative` had to exclude. Each majorant case is a single
     `MDom` closure — `MDom-succ`/`MDom-id` (oracle, `Succ`), `MDom-const-left`
     (partial recursor `orbit ⊕ ν`, its orbit `< ε₀` by `MDom-orbit-<-ε₀`),
     `MDom-∘` (composition), `MDom-const` (constant), and `MDom-recursor-diag`
     (the new diagonal). The relation's two recursor cases both bound the orbit
     termwise then close with `Conditional.height-iter-≤-orbit-bound`; for
     `iterDiagF` the orbit is over the argument itself (base case = the
     hypothesis `height d ≤ a`) and the count is `⟦G⟧ d`. Payoff
     `height-<-ε₀`, and `height-recursor-diag-<-ε₀`: the tower-driving diagonal
     driven by an arbitrary ground count (an oracle read, so the orbit sup is
     genuinely taken) has height `< ε₀` — unconditional, the term `Applicative`
     could not reach. Two leaves `MDom-const`/`MDom-const-left` were added to
     `MultDominated` for the constant and left-additive majorants. Honest
     scope: still a *fragment* (the functions `MDom` is closed under, and the
     specific `S`-diagonal whose start is the bound variable), strictly larger
     than `Applicative`'s; the full conjecture still needs the type-indexed
     hereditary assembly over all first-order types.

(31) `DialogueTreeHeight.MultApplicativeT` — **the reality-check: the
     `MultApplicative` fragment embeds into genuine first-order System T.** Its
     bespoke `Gnd`/`Fun` syntax and interpretation `⟦_⟧G`/`⟦_⟧F` are certified
     to denote actual `T₁` terms (`Majorant`'s `Ω/Zero/Succ/Iter/K/S/·`) via a
     translation `⌜_⌝G`/`⌜_⌝F` with an agreement proof `⟦ ⌜ x ⌝ ⟧₁ ＝ ⟦ x ⟧`.
     The agreement is *definitional* at every node (`zero' = η 0`,
     `succ' = B-functor succ`, `iter' f x = kleisli-extension (iter f x)`,
     `Ķ x y = x`, `Ş f g x = f x (g x)`), so the proof is `refl` glued by
     `ap`/`happly`/funext. Two translations confirm the fragment is honest:
     composition `compF f g` becomes `S (K f) g`, and — the point — the
     recursor `S`-diagonal `iterDiagF φ G` becomes **`S (Iter φ) G`**, a genuine
     use of the `S` combinator with `Iter φ` as the shared-argument function. So
     the tower-driving term really is a System T term, and the payoff
     `height-systemT-<-ε₀ : height ⟦ ⌜ x ⌝G ⟧₁ < ε₀` states `MultApplicative`'s
     bound directly about System T dialogue trees. This does not enlarge what is
     proved; it pins the *scope* — the fragment is a bona fide sub-language of
     `T₁`, not an ad-hoc calculus.

(32) `DialogueTreeHeight.MultHereditary` — **the hereditary predicate whose
     recursor closes.** Runs the `Hereditary`/`CNFTransformer` skeleton
     (`GroundType`, `FunArgs`, `plug`, and the mutual `𝔅M`) with the ground joint
     bound taken to be the `MDom` bound `(s ⊕ c) ⊗ M` for a `ValidMult` `M`
     (`JBM`/`JointM`), in place of the finite affine `(s ⊕ d) ⊗ ι[m]`. Ground
     extraction `𝔅Mι-to-<ε₀`/`<ε₀-to-𝔅Mι` lands at `ε₀` (`s = Z` gives
     `c ⊗ M < ε₀`). Application (`𝔅M-app`, absorbing a ground argument into the
     constant via `JBM-shift`), the base combinators, weakening, `K`
     (`𝔅M-K`) and the higher-type `S`-diagonal (`𝔅M-S-higher`) all port
     essentially verbatim. **The new content is `𝔅M-Iter`**: the recursor
     majorant `μ-Iter` is good — the case `Hereditary`/`PolyHereditary`/
     `PolyTransformer`/`CNFTransformer` all left open. It closes in one line: at
     the function argument `g`, `𝔅M (ι ⇒ ι) g` hands back (via `JointM1→MDom`)
     exactly the `MDom` data `MultDominated.MDom2-Iter` consumes, giving the
     joint bound for `λ a ν → L (λ k → iter g a k) ⊕ ν` — because the `MDom`
     shape survives its own orbit. And **the ground `S`-diagonal at `ι`**
     (`𝔅M-S-ground-ι`, `λ a → φ a (γ a)` with `φ : ι⇒ι⇒ι`, `γ : ι⇒ι`) closes via
     `MDom2-diag`. Small `JointM`⟷`MDom`/`MDom2` conversions witness that the
     common-bound joint form and the per-argument classes coincide at arity 1
     and 2. Honest scope: this closes application, `K`, `S`-higher, the base
     combinators, the **recursor**, and the ground `S`-diagonal *at `ι`* — a
     strict advance over `CNFTransformer` (which had every case *except* the
     recursor). What remains for a fundamental theorem over all of `T₁` is the
     general ground `S`-diagonal (shared argument `ι`, the other two arguments at
     higher types) — the same combinatorial case open throughout, now the *sole*
     gap, the previously-hard recursor half discharged.

(33) `DialogueTreeHeight.MultHereditaryT` — **a fundamental theorem: unconditional
     `height < ε₀` for first-order System T with the recursor AND `S` (except
     ground-`S` with function-typed components).** Assembles `MultHereditary`'s
     closures into a term induction and connects it to real dialogue height. The
     enabling observation: the `S` *combinator* `𝔅M (S-type) μ-S` closes at
     exactly the instances `MultHereditary` handles — at `((ι⇒ι⇒ι)⇒(ι⇒ι)⇒ι⇒ι)`
     it is `𝔅M-S-ground-ι` (both non-shared and the shared argument sit in
     `FunArgs`, leaving the ground diagonal), and at any function-typed shared
     argument it is `𝔅M-S-higher` (lemmas `𝔅M-Sg`/`𝔅M-Sh`, each a one-line peel
     of the `FunArgs` tuple). The fragment `T★` has `S` at those two families
     (`Sg★`, `Sh★`), plus `Ω/Zero/Succ/Iter/K/·`; it embeds into `Majorant.T₁`
     (`e`, both `S` to `S₁`). `goodμ : (t : T★ σ) → 𝔅M σ (μ (e t))` is one
     `MultHereditary` closure per case; then `𝔅Mι-to-<ε₀` gives `μ (e t) < ε₀`
     and `Majorant.height-≤-μ` gives `height ⟦ e t ⟧₁ ≤ μ (e t)`, so
     `height-<-ε₀ : height ⟦ e t ⟧₁ < ε₀` and `dialogue-height-<-ε₀` for a
     functional `t : T★ ((ι⇒ι)⇒ι)`. This is the first fundamental theorem to
     include the recursor *and* `S` at higher types at the `ε₀` bound — the
     recursor being the previously-open half. (`MultHereditary` had to switch its
     `Maj` import from `Hereditary` to `Majorant` so the two `Maj` definitions
     coincide, letting `μ`/`μ-S` meet `𝔅M`.) Honest scope: still not all of `T₁`
     — ground-`S` with a function-typed `σ`/`τ` is the sole excluded combinator,
     the persistent structural wall.

(34) `DialogueTreeHeight.MultHereditaryB` — **Design B: the dual `s`-relative
     logical relation — closing ground-`S` at a function-typed argument, the case
     `MultHereditary` (Design A) could not reach.** Where Design A records
     function arguments as *global* majorants (quantified before the common bound
     `s`), Design B uses an `s`-relative relation `Bnd σ s c M φ`: ground
     arguments measured against `s` with unchanged data `(c,M)`, function
     arguments carrying their **own** data `(cg,Mg)` that threads multiplicatively
     to `M ⊗ Mg` (as in `MDom-∘`). Because a function argument is fed with its
     actual `s`-relative bound rather than a global majorant, the headline
     **`Good-S-fun`** — ground-`S` `λ a → φ a (γ a)` with `γ a` *function-valued*
     — closes directly, multiplier `Mφ ⊗ Mγ`, with **no monotonicity
     hypothesis**; that is exactly the combinator Design A provably could not
     close. Function-argument application (`Good-app-fun`), ground extraction at
     `ε₀`, and the base combinators close too. **Honest dual scope:** the
     `s`-relative bound holds only for inputs `≤ s`, so Design B cannot bound
     anything probing a function argument *outside* `[0,s]` — namely the
     **recursor** (iterating `g` runs it past `s`) and **ground-argument
     application** before a function argument (`Bnd` is antitone in `s` at
     function-argument slots) — precisely the cases Design A *does* close. So A
     and B are complementary: each closes what the other cannot. The shared
     obstruction — one relation that is `s`-relative *and* order-insensitive *and*
     lets a function-argument bound depend on the preceding ground context — is
     the genuine Howard–Bezem strong-majorizability step, now pinned from both
     sides.

(35) `DialogueTreeHeight.MultHereditaryE` — **Design E: transformer-valued
     bounds — ground-`S` at a function type for *super-linear* companions,
     strictly beyond `MultHereditaryB`.** B carries a fixed multiplier
     (`(weight ⊕ c) ⊗ M`, linear), which cannot even *express* a functional like
     `γ a = λ x → a ⊗ x` whose ground-`S` diagonal is `a ⊗ (a ⊗ a) = a³`. Design E
     replaces the fixed multiplier with a **monotone, `< ε₀`-preserving
     transformer** `T : 𝓑 → 𝓑` (`ValidT`, closed under composition; the
     super-linear `ValidT-sq : ValidT (λ w → w ⊗ w)` is exhibited). The ground
     bound is `a ≤ T w`, a function argument carries its own `Tg`, and the result
     transformer is the composition `T ∘ Tg`. So application (`Good-app-fun`) and
     **ground-`S` at a function type (`Good-S-fun`, with payoff `Good-S-fun-<ε₀`)
     close for arbitrary `ValidT` companions — including super-linear ones** — a
     strict extension of B's reach. Honest scope: transformers fix the bound
     *shape*, not the *quantification order*. The A/B fork is unchanged —
     function arguments good at the *same* weight (here and B: ground-`S` closes,
     recursor does not) vs *globally* (A: recursor closes, ground-`S` does not),
     with `γ a` provably good only at weights `≥ a` and no transformer bridging
     `w′ < a`. So Design E is "B, super-linear": it widens the ground-`S`/
     application reach but inherits B's recursor gap. `ValidT` deliberately omits
     orbit-closure — that omission *is* the recursor's residual, and closing the
     whole gap still needs the order-free, ground-context-dependent Howard–Bezem
     predicate.

(36) `Claude.BrouwerOrdinals.MultSquareOrbit` — **super-linear orbit-closure: the
     orbit of squaring `b ↦ b ⊗ b` is `< ε₀`.** The reframe's recursor half needs
     the base transformer class orbit-closed *and* super-linear (the `S` side,
     `MultHereditaryE`, already needed super-linear bounds). `Affine`'s
     `double-orbit-<-ε₀` does the *linear* doubling `b ↦ b ⊕ b (= b ⊗ ι[2])`;
     this does the *degree-two* `b ↦ b ⊗ b`. Key: squaring adds only one level to
     the `ω`-exponent per step — `w ≤ ω^ b ⇒ iter sq w k ≤ ω^(b ⊗ ι[2ᵏ])` (via
     the exponent homomorphism `ω^ x ⊗ ω^ x = ω^(x ⊕ x)`, `ω^⊗`), so the sup is
     `ω^(b ⊗ ω) < ε₀` (`sq-orbit-<-ε₀`). Helpers `≤-S-self` (`a ≤ S a`), `expo`/
     `tower-≤-ω^expo` (`w < ε₀ ⇒ w ≤ ω^ b`, `b < ε₀`). This makes the arithmetic
     boundary concrete: squaring's orbit stays `< ε₀` (a bounded exponent
     multiple), whereas `ω`-exponentiation's orbit reaches `ε₀` (it moves up a
     tower level) — so the reframe's base transformer class can contain squaring
     but must exclude `ω^`. With `MultHereditaryE` (super-linear on the `S` side)
     this shows both arithmetic pieces of a super-linear transformer class are
     tractable — evidence the reframe's residual is arithmetic, not another
     structural wall.

(37) `DialogueTreeHeight.MultHereditaryF` — **the type-indexed higher-order
     transformer: the structural A/B fork DISSOLVED.** The whole project's wall
     was that a function argument had to be good either at the current weight
     (ground-`S` closes, recursor fails) or globally (recursor closes, ground-`S`
     fails), with `γ a` good only at weights `≥ a`. Resolution: every argument
     carries its **own** transformer, itself globally valid (`GoodT`). Transformers
     are type-indexed (`𝕋 ι = 𝓑→𝓑`, `𝕋(σ⇒τ) = 𝕋σ→𝕋τ` — functionals on
     transformers); the bound is `Bnd ι w T a = a ≤ T w`, an application feeds the
     argument with its transformer *at every weight* and forms the higher-order
     application `T Tg`. Because an argument's transformer `Ta` is globally valid,
     feeding `(a, Ta)` to `Good γ` *at every weight* makes `γ a` globally good with
     transformer `Tγ Ta` — the "good only at `≥ a`" obstruction vanishes. So the
     **general ground-`S` diagonal `Good-S-diag` closes for ARBITRARY `σ, τ`
     (including function-typed `σ` — the case blocked throughout)**, alongside
     `Good-app`, ground extraction, and the base combinators, all in a predicate
     that feeds globally (recursor-compatible). The **recursor `Good-Iter`** also
     closes: its transformer is the functional orbit `Torbit Tg Ta = λ w →
     L (λ k → iter Tg Ta k w)`; the pointwise orbit bound holds by induction
     (`orbit-pt`, using `GoodT` preserved along `Tg`), so its `Bnd` closes
     unconditionally and only its `GoodT` component needs the transformer to stay
     `< ε₀` — taken as the explicit hypothesis `orbit-good`. `Good-K` and the
     **full `Good-S`** (general `ρ σ τ`, shared argument possibly function-typed)
     close *unconditionally*, so every combinator except the recursor is
     unconditional. So Design F converts the structural wall into a single
     **transformer-orbit-closure** statement. **Honest caveat:** `orbit-good` is
     *false* for the full `GoodT` — the exponentiation functional `Tg T = λ w →
     ω^(T w)` is `GoodT` but its orbit reaches `ε₀` — so the residual is to cut
     `GoodT` down to a sub-exponential orbit-closed subclass (containing `⊕`, `⊗`,
     squaring per `MultSquareOrbit`, but excluding `ω^`) on which it holds, and
     land the combinators there; `Good-Iter` is over the full `GoodT` only to
     expose the reduction. Honest scope: not yet a fundamental theorem — the
     sub-exponential class + height connection remain — but the type-structural
     obstruction that stood the whole project is gone; what is left is ordinal
     arithmetic and assembly, not type structure.

(38) `DialogueTreeHeight.MultHereditaryFLin` — **discharging `MultHereditaryF`'s
     recursor hypothesis on the linear class, via the `MDom` orbit engine.**
     `Good-Iter`'s `orbit-good` is false for the full `GoodT` (the `ω^` functional),
     so it must be discharged on a sub-exponential subclass. Here that subclass is
     the **linearly-bounded** functionals `LinBounded Tg = Σ c M, c < ε₀ ×
     ValidMult M × (∀ T w → Tg T w ≤ (T w ⊕ c) ⊗ M)` — the shape a recursor with a
     linear body (identity/successor/oracle-relabel and composites) produces.
     **`orbit-good-lin`**: for a `GoodT`, `LinBounded` functional, `Torbit Tg Ta`
     is `GoodT` — iterating `Tg` on `Ta` is dominated pointwise by iterating the
     `MDom` body `b ↦ (b ⊕ c) ⊗ M` on `Ta w` (`iter-bound`), so
     `MultAffine.mbody-orbit-≤` bounds the orbit by `(Ta w ⊕ c) ⊗ ω^(M ⊗ ω) < ε₀`;
     monotonicity comes from `GoodT-iter`. So the recursor's orbit-closure is
     genuinely provable on a real class from arithmetic already in the library —
     concrete proof the `MultHereditaryF` residual is arithmetic, not structural.
     The same pattern reaches the super-linear transformers with `MultSquareOrbit`
     in place of `mbody-orbit-≤`. The linear functionals form a **complete
     algebra**: `LinBounded-id`, `LinBounded-S`, `LinBounded-∘` (composition, via
     the `MDom-∘` enlarge-then-`crux` technique — constants accumulate `c_g ⊕ c_f`,
     multipliers compose `M_g ⊗ M_f`) and `LinBounded-orbit` — exactly the `ι ⇒ ι`
     transformers a linear first-order term builds by composition and the recursor.
     Remaining assembly toward a fundamental theorem: a `Design-F` predicate
     carrying this class on `ι ⇒ ι` transformers, threaded through the combinators
     — note `K` yields a *constant* function whose transformer is not `LinBounded`
     (it ignores its argument) though its orbit is trivially bounded, so the class
     must be broadened. The recursor orbit-closure is now discharged for the three
     basic body shapes a first-order term generates: `orbit-good-lin` (linear, via
     `mbody-orbit-≤`), `orbit-good-const` (constant, from `K`), and
     `orbit-good-add` (the partial recursor's own transformer
     `λ Tν → λ w → C w ⊕ Tν w`, left-additive, via `Nested.orbit-left-sup-≤` — what
     a *nested* recursor iterates). Composition cross-cases (`lin ∘ add`, …) yield
     a two-sided affine shape `D₁ ⊕ (T ⊕ c) ⊗ M ⊕ D₂`, so the fundamental theorem's
     transformer class unifies these into that form, closed under composition (the
     non-commutative affine arithmetic) and orbit; then the height connection.

(39) `DialogueTreeHeight.MultHereditaryFAff` — **the affine transformer class:
     the complete `ι ⇒ ι` transformer algebra of the first-order fragment.**
     The two-sided shape of (38) is resolved by placing the additive summand
     *inside* the multiplied zone from the start: `AffBounded Tg = Σ D c M,
     GoodT D × c < ε₀ × ValidMult M × (∀ T w → Tg T w ≤ (D w ⊕ (T w ⊕ c)) ⊗ M)`
     — the **inner-affine** functionals. Nothing ever needs to escape a
     multiplier (`⊕` non-commutative below `ε₀`, `⊗` not left-distributive: a
     `D` trapped inside `⊗ M` genuinely cannot move out — so it is defined in).
     The three shapes of (38) embed (`AffBounded-lin/const/add`, plus `id`, `S`),
     and the class is **closed under composition** (`AffBounded-∘`): the outer
     summand and constant are absorbed into the enlarged inner zone `Y′` by a
     triple absorption `Y′ ⊕ (Y′ ⊕ Y′) ≤ Y′ ⊗ ω` (`⊕-trip-≤-⊗ω` — replacing
     `crux` at the price of one `ω` factor), multiplier `M_g ⊗ (ω ⊗ M_f)`; and
     **closed under the recursor orbit** (`AffBounded-orbit`): iteration is
     dominated by the `MDom` body `b ↦ (b ⊕ c) ⊗ (ω ⊗ M)` from start
     `D w ⊕ T w`, carrying the invariant that the majorant stays above `D w`
     (`aff-orbit-≤`, no `GoodT` needed for the bound), so `mbody-orbit-≤` gives
     the raised multiplier `ω^((ω ⊗ M) ⊗ ω)` — same `D`, same `c`, still
     `ValidMult`. Payoff **`orbit-good-aff`**: the orbit transformer of a
     `GoodT`, inner-affine functional is `GoodT` — the recursor's orbit-closure
     hypothesis holds uniformly on the whole class, subsuming the three
     per-shape discharges of (38). The transformer-class *arithmetic* for the
     first-order fragment is thereby complete; what remains for its fundamental
     theorem is plumbing (a `Good`-style relation over a concrete first-order
     syntax carrying `AffBounded` at `ι ⇒ ι`, then the height connection via
     `Majorant`). Honest scope: the conjecture for full System T remains open —
     genuinely super-linear transformers (squaring, `ω^`) lie outside this
     class; `MultSquareOrbit` bounds their orbits individually but no closed
     class containing them is known.

(40) `DialogueTreeHeight.MultHereditaryFT` — **a fundamental theorem from
     Design F: unconditional `height < ε₀` including a previously-blocked
     ground-`S` family.** Joins (37) and (39): the Design-F predicate refined
     so `ι ⇒ ι` transformers carry `AffBounded` — `LA ι = GoodT ι`,
     `LA (σ⇒τ) = (maps LA to LA) × ExtraA σ τ`, with `ExtraA ι ι = AffBounded`
     and trivial elsewhere, *matching the codomain first* so the obligations in
     `K`/`S` (arrow codomains) reduce at abstract types. `BndA`/`GoodA` are
     (37)'s `Bnd`/`Good` with `LA` for `GoodT`; structural proofs port
     verbatim; the refinement is paid at exactly four spots, each a (39)
     lemma: `Succ ↦ AffBounded-id`, `Ω ↦ AffBounded-S`, `K`'s inner constant
     `↦ AffBounded-const`, recursor partial application `↦ AffBounded-add`,
     and the orbit's `GoodT` by `orbit-good-aff` — so **the recursor is
     unconditional in the predicate** (no orbit hypothesis: the iterated
     argument's own `LA` supplies `AffBounded`). Fragment `T⁺`:
     `Ω/Zero/Succ/Iter/K/·` and `S` at `Sh⁺` (shared argument function-typed,
     as `T★`) **plus the new `Sf⁺`: shared argument `ι`, function-typed
     result, arbitrary middle type** — a member of the blocked family "ground
     `S` with function-typed `σ` or `τ`" that no `Maj`-level design could
     close; here its obligations reduce to `𝟙` and Design F's transformer
     mechanism does the rest. Payoffs `μ-<-ε₀`, `height-<-ε₀`, and
     `dialogue-height-<-ε₀ : (t : T⁺ ((ι⇒ι)⇒ι)) → height (⟦ e t ⟧₁ generic)
     < ε₀`, all unconditional. Honest scope: `T⁺` does not include `T★`'s
     all-ground `Sg★` (needs a *joint* binary affine bound) nor ground-`S`
     with function-typed middle and ground result (needs affine data depending
     on the function argument — Howard's transformer tower); unifying `T★`
     and `T⁺` needs the `n`-ary joint refinement. The full conjecture remains
     open.

(41) `DialogueTreeHeight.MultHereditaryFAff2` — **the binary joint affine
     class `Aff₂`: two ground transformer arguments inside one multiplied
     zone.** The data the all-ground `S` diagonal needs, which no curried
     bound can supply (the classical joint-bound move of `Hereditary`, lifted
     to the transformer level): `Aff₂ T = Σ D c M, … × (∀ T₁ T₂ w → T T₁ T₂ w
     ≤ (D w ⊕ (T₁ w ⊕ (T₂ w ⊕ c))) ⊗ M)`. The zone is quasi-commutative —
     reordering/duplication costs a factor of `ω` (`⊕-quad-≤-⊗ω`,
     `S-≤-⊗ω` joining (39)'s dup/trip) — which gives the closure algebra:
     `Aff₂-apply` (currying: fixing the first argument is `AffBounded` with
     summand `D ⊕ T₁`, pure `⊕`-associativity), `Aff₂-K` and `Aff₂-insert`
     (the projections), `Aff₂-Iter` (the recursor's start and count jointly,
     from `AffBounded-orbit` plus `S M ≤ M ⊗ ω`), and the payoff
     **`AffBounded-Sg-diag`**: from `Aff₂ Tφ` and `AffBounded Tγ` the ground
     diagonal `λ Ta → Tφ Ta (Tγ Ta)` is `AffBounded` — substitute `Tγ`'s
     bound into `Tφ`'s zone, enlarge, quad-absorb. Capping at two arguments
     is real: an all-ground *binary* result would demand `Aff₃`, and the
     arities ladder with no uniform top here.

(42) `DialogueTreeHeight.MultHereditaryFJT` — **the joint fundamental
     theorem: unconditional `height < ε₀` for a fragment `T₂ ⊇ T★` that also
     has the function-typed ground-`S` families.** The (40) refinement
     extended one arity rung: `Extra ι ι = AffBounded`, `Extra ι (ι ⇒ ι) =
     Aff₂`, trivial elsewhere — now matching the *domain* first (arrow
     domains carry nothing at abstract codomains; the price is that ground
     domains see the codomain's shape, so the `Sf⁺` family splits in two).
     `LJ`/`BndJ`/`GoodJ` port from (37)/(40); new joint obligations paid by
     (41): `K`'s outer projection (`Aff₂-K`), `K` at `σ = ι ⇒ ι`
     (`Aff₂-insert`), the recursor's two ground arguments (`Aff₂-Iter`), and
     the all-ground `S` diagonal (`AffBounded-Sg-diag`) — so **both the
     recursor and the all-ground `S` are unconditional in the predicate**.
     Fragment `T₂`: `Ω/Zero/Succ/Iter/K/·` and four `S` families — `Sg₂`
     (all-ground, = `Sg★`), `Sh₂` (shared argument function-typed, = `Sh★`),
     `Sfh₂`/`Sfr₂` (the (40) `Sf⁺` split by result shape). `T₂ ⊇ T★` is
     witnessed by `emb★` with `emb★-coherent` over the `T₁` semantics, and
     `T₂ ⊋ T★` since `Sfh₂`/`Sfr₂` lie outside `T★`'s families. Payoffs
     `μ-<-ε₀`, `height-<-ε₀`, `dialogue-height-<-ε₀`, all unconditional —
     the largest fragment with the `ε₀` bound in this development. Honest
     scope: `T₂` misses exactly one (40) instance family — `Sf⁺` at result
     `ι ⇒ ι` (diagonal an all-ground binary function), whose obligation is
     an `Aff₂` requiring *ternary* joint data (`Aff₃`) on `φ`; the `n`-ary
     zone-calculus ladder is the visible next rung. Also still outside:
     ground-`S` with function-typed middle and ground result (Howard's
     transformer tower), and the super-linear transformers. The full
     conjecture remains open.

(43) `DialogueTreeHeight.MultHereditaryFAffN` — **the type-level joint zone
     calculus: the whole `Affₙ` arity ladder in one recursion on the type.**
     `BoundT τ T D c M` accumulates each ground argument into the left
     summand `D` and bounds the ground value by `(D w ⊕ c) ⊗ M`; at a
     *function-typed* argument it collapses to `𝟙` (no joint data across a
     function argument — that would be the transformer tower), so the data is
     substantive exactly on the all-ground prefix and trivially dischargeable
     beyond (`Collapses`, `BoundT-collapse`). `JAff τ T` packages the usual
     side conditions. Currying is *definitional* (feeding an argument is the
     recursion itself); `JAff-id/S/const/add/K-outer/insert/Iter` are the
     combinator shapes, generalizing their (39)/(41) versions. The engine is
     **`BoundT-absorb`**: re-basing the accumulated summand from `A` to `B`
     when `A ≤ (B ⊕ c′) ⊗ K`, paying one successor of `K` per remaining
     ground argument (the definitional identity `X ⊗ S K = X ⊗ K ⊕ X`),
     total `K ⊕ ι[depth+1]`, weakened to `K ⊗ ω` by `⊕ι-≤-⊗ω`. Payoff
     **`JAff-Sg-diag`**: for *any* result type `τ`, from `JAff (ι⇒ι⇒τ) Tφ`
     and `JAff (ι⇒ι) Tγ` the ground diagonal `λ Ta → Tφ Ta (Tγ Ta)` is
     `JAff (ι⇒τ)`, at the same multiplier `((Mγ⊗ω)⊗ω)⊗Mφ` as (41)'s
     `τ = ι` case — every rung of the ladder in one statement.

(44) `DialogueTreeHeight.MultHereditaryFNT` — **the all-ground-`S`-complete
     fundamental theorem: fragment `T₃` with the ground-`S` diagonal at every
     result type, unconditional `height < ε₀`.** The refinement is one clause
     pair: `ExtraN ι τ = JAff (ι ⇒ τ)`, arrow domains trivial — `JAff`'s own
     collapse makes a single uniform predicate viable where (40)/(42) needed
     type-by-type case analysis. Combinator obligations: `Succ/Ω ↦
     JAff-id/S`; `K` outer `↦ JAff-K-outer`, inner by the shape of `σ`
     (`JAff-const`/`JAff-insert`/collapse); recursor `↦ JAff-Iter` +
     `JAff-add` + `orbit-good-aff` (via `JAff-to-AffBounded`) —
     unconditional. Fragment `T₃`: `Ω/Zero/Succ/Iter/K/·` and three `S`
     families — **`Sg₃ {τ}`: shared `ι`, middle `ι`, ANY result type `τ`**
     (diagonal = `JAff-Sg-diag`; `τ = ι` is `Sg★`, `τ = ι ⇒ ι` is the family
     (42) documented as needing `Aff₃`, and so on through every arity and
     all mixed `τ`), `Sh₃` (shared argument function-typed), and `Sx₃ {σ} {τ}`
     (shared `ι`, any middle `σ`, with a `Collapses τ` witness). `T₃ ⊇ T★`
     via `emb★`/`emb★-coherent`, strictly. Payoffs `μ-<-ε₀`, `height-<-ε₀`,
     `dialogue-height-<-ε₀`, all unconditional. Honest scope: the remaining
     `S` family is shared `ι`, function-typed middle `σ`, all-ground `τ` —
     real joint data depending on the function argument's own data (Howard's
     transformer tower). The fragments are genuinely *incomparable* at that
     frontier: `T⁺`/`T₂` contain some such instances precisely because their
     coarser predicates demand no data at the diagonal's type, while `T₃`'s
     finer predicate (which buys every all-ground `S`) demands data there
     that cannot be produced; no single fixed-data predicate can have both,
     and their join is the transformer-tower step. Super-linear transformers
     also remain outside. The full conjecture remains open.

(45) `DialogueTreeHeight.MultHereditaryG` — **Design G, the transformer
     tower's ground layer: Howard-style data maps over the Design-F
     transformers.** Mirroring (37) one level up, every argument carries its
     own *data*: `𝔻 ι = GFun` (a `GoodT` bound function — ground
     transformers are their own data, `selfD`), `𝔻 (σ⇒τ) = 𝔻 σ → 𝔻 τ`,
     with `BndD` the pointwise Howard-shaped bound relation. Payoff of the
     shape alone: **the structural half is free — `BndD-S` closes for ALL
     `ρ, σ, τ` in one line** (the diagonal's data is application
     `(dφ da)(dγ da)`), likewise `BndD-K`; the instance-splitting of
     (40)/(42)/(44) was an artifact of fixed data. The residual concentrates
     in the recursor, exactly as (37)'s `orbit-good`: arbitrary data maps
     have unbounded orbits (`ω^`-composition is a legal `𝔻 (ι⇒ι)`), so maps
     must be **tracked** — dominated by an inner-affine bound-transformer
     (`Tracked`, the `AffBounded` shape read on bound functions) — and the
     entire (39) affine calculus transfers by reuse: `Tracked-∘` is
     `AffBounded-∘` on the dominating transformers; **`BndD-orbit`** bounds
     the recursor's data orbit via `aff-orbit-≤` (giving `dOrbit`,
     `Tracked-dOrbit` — nested recursion stays tracked, one `ω`-exponent
     per level), and `BndD-Iter` assembles the recursor. **KEY STRUCTURAL
     FINDING (the honest one): the tower is SELF-SIMILAR.** A fundamental
     theorem must carry `Tracked` hereditarily (a tracking relation `𝕂` on
     data), and `𝕂`'s own `S`-diagonal at function-typed middle demands
     tracking *of tracking* — each storey's diagonal needs the next storey,
     because a term's data map has the same combinator structure as the term
     itself. Any fixed number of storeys reproduces the (44) fragment
     lattice shifted one level; `T₁`-completeness needs the whole tower.
     Two candidate routes are pinned: (i) an ℕ-indexed tower predicate
     `𝕂 n` (each term needs only finitely many storeys — its own depth —
     so a level-polymorphic fundamental theorem `∀ t → Σ n , tracked to
     depth n` is in reach; levels ≥ 2 appear structurally identical, all
     being affine-data maps, so the storeys may collapse to one
     self-referential level); (ii) Howard's actual route — a syntactic
     ordinal *assignment* rather than a logical relation. The conjecture
     remains open.

(46) `Claude.BrouwerOrdinals.MultBump` — **the per-storey multiplier arithmetic
     of the Howard tower.** In the level-indexed tracking design (design
     note `dialogue-tree-height-howard-tower.md`), a function argument
     contributes its additive part to the consumer's zone like a ground
     argument, and its multiplier through a multiplier map; the maps a
     first-order term generates are exactly the finite iterates of the
     recursor's raise, `bump M = ω^ ((ω ⊗ M) ⊗ ω)` (the multiplier of
     `AffBounded-orbit`/`Tracked-dOrbit`, definitionally —
     `orbit-raise-is-bump` is `refl`). The ℕ-indexed family `bumpk k` has
     the closure laws the storeys need: `ValidMult`-preservation,
     monotonicity in both arguments, inflationarity (`≤-bump`), `< ε₀`
     (`bumpk-<-ε₀`), and the absorptions — `⊗-≤-bump : X ⊗ X ≤ bump X`
     (via inflationarity `≤-ω^` and the exponent homomorphism `ω^⊗`), and
     `bumpk-⊗-absorb`: two arguments' multipliers, each used any finite
     number of times, are absorbed by one bump of their `⊕`-join. So the
     storey accounting is: composition free, products one bump, recursor
     nesting `k ↦ succ k` — one `ω`-exponent per storey, `ε₀` as the join.

(47) `DialogueTreeHeight.MultHereditaryG2` — **Design G's second storey,
     first consumption point: the data-level ground-`S` diagonal.** Joint
     binary tracking `Tracked₂` (the `Aff₂` shape on bound functions) with
     its algebra (`Tracked₂-apply` — currying joins the fixed argument's
     bound into the summand; `Tracked₂-K`, `Tracked₂-insert`), and the
     payoff **`Tracked-diag`**: for `F` jointly tracked and `G` tracked,
     the ground diagonal `λ b → F b (G b)` is tracked — proved, like
     `Tracked-∘`, by pure reuse: the dominating transformers `Taff₂`/`Taff`
     are `Aff₂`/`AffBounded` by construction (`≤-refl`), (41)'s
     `AffBounded-Sg-diag` closes their diagonal, and the data-level bound
     rides along by monotonicity. With (46) this completes the *arithmetic*
     for the two-storey collapse of the Howard tower; the remaining
     construction is the tower predicate itself (`Trk`, mutual with a
     zone-bound recursion over types, fn-arg positions consuming the
     argument's tracking data additively + one bump) and the
     level-polymorphic fundamental theorem over full `T₁`. The conjecture
     remains open.

(48) `DialogueTreeHeight.MultHereditaryH` — **Design H, stage 1: the Howard
     tower predicate — the tracked-data hierarchy `𝕂`, defined.** The
     level-free form of the tower: `𝕂 ι` is a good bound function,
     `𝕂 (σ⇒τ)` a map `𝕂 σ → 𝕂 τ` with a **zone pack** `(D, c, M, j)` —
     joint affine zone, multiplier pool, bump budget. The bound relation
     threads three accumulators through the argument spine: the additive
     zone `A` (ground arguments contribute their bound functions, function
     arguments their packs' additive parts `kadd`), the multiplier pool
     `MH` (`kmult`), and the bump budget `JH` (`kbudget`); at ground,
     `pr₁ k w ≤ ((D w ⊕ (A w ⊕ c)) ⊗ bumpk (j + JH) (M ⊕ MH))` — one zone
     multiplied by the pooled multipliers under the pooled budget, which is
     exactly what (46)'s absorption laws service. **The decisive clause is
     `PackDom`: the bound constrains the packs of partial applications** —
     additive part dominated by the current zone, multiplier by the current
     pool, budget by the current budget (in semantic `bumpk` form, avoiding
     ℕ-order) — the "rigid multiplier" invariant held by the shape of the
     predicate. This is what terminates (45)'s self-similar regress: the
     pack of `γ a` is *forced* to be affine in `a`'s bound with fixed
     multiplier data, so the ground-`S` diagonal at function-typed middles
     assembles its pack arithmetically ((41)/(47) pattern) instead of
     demanding another storey. Mutual structural recursion
     (`𝕂`/`ZPack`/`ZApply`/`ZCont`/`PackDom`, argument and result types
     both proper subterms — `ZApply` consumes one argument, `ZCont`
     continues), accepted by the termination checker; plus the weakening
     toolkit `ZCont-mono-A`/`ZApply-mono-A` (no contravariance: argument
     data is universally quantified). Stage 2 — the combinator packs, the
     bound relation to Design-F transformers, and the fundamental theorem
     over full `T₁` — is the remaining construction. The conjecture remains
     open.

(49) `DialogueTreeHeight.MultHereditaryH2` — **Design H, stage 2a: the
     rebase arithmetic.** The inequality layer for re-basing tower bounds:
     budget ℕ-arithmetic (`+ℕ-succ-right/comm/assoc/shuffle`), the `bumpk`
     calculus (`bumpk-+` composition, inflationarity `≤-bumpk`,
     `bumpk-pad`, the `ω`-floor `ω-≤-bump` via `S Z ⊗ y ＝ y`, and
     `B-step`: a trailing `⊗ ω` is one bump), the **zone-extension lemma
     `zdom-ext`** (adding the same summand to both accumulators preserves
     base domination at cost `⊗ ω`: three summands, each below the extended
     zone times the old multiplier, packed by the triple absorption), the
     **pool-extension lemma `pool-ext`** (joining the same multiplier to
     both pools costs one slack unit — a duplication absorbed by one bump),
     and the spine-computed rebase budget `rbb`. The key design point,
     recorded in the preamble: stating the pool domination on the *raw*
     pool with explicit slack `e` is what prevents the bumps-of-bumps
     explosion a bumped pool hypothesis would cause — pool substitution
     costs an additive budget shift only.

(50) `DialogueTreeHeight.MultHereditaryH3` — **Design H, stage 2b: the
     rebase — the tower's load-bearing lemma.** `ZCont-rebase`/
     `ZApply-rebase`, by mutual induction on the type: a `ZCont` bound
     obtained under one pack (an argument's) converts to a bound under
     another (the consumer's), given the four invariants — base domination
     `I1` at budget `(u + e) + JH′`, raw pool domination `I2` at slack `e`,
     semantic budget domination `I3`, `ω`-floor `I4` — with the step
     discipline: a ground argument costs `u ↦ succ u` (`zdom-ext` + one
     bump, and `I3` weakens by one bump), a function argument additionally
     `e ↦ succ e` (`pool-ext`), pools and budgets extending *in tandem* on
     both sides (`I2`/`I3` re-derived via `bumpk-+` and the ℕ-shuffles);
     the ground case merges base and pool factors by `mult-rebase` +
     `⊗-≤-bump` — one final bump. The concluding pack budget is `rbb τ u e`,
     whose definition makes the recursive calls match **definitionally**;
     `PackDom` components re-base by the same chains, padded via the
     splitting lemmas `rbb-split`/`rbb-split-u`. With this lemma the
     remaining stage — the combinator packs (each an instantiation of an
     argument's pack followed by a rebase) and the fundamental theorem over
     full `T₁` — is assembly. The conjecture remains open.

(51) `DialogueTreeHeight.MultHereditaryH4` — **Design H, stage 2c: the
     fundamental-theorem skeleton.** The three-layer predicate: `BndL`
     (majorants bounded by transformers at every weight — Design F's `Bnd`
     with `LT` arguments), `LT σ T` = maps `× Σ k ꞉ 𝕂 σ , BndH σ T k`
     (`LT ι = GoodT ι`), and the Howard-shaped `BndH` tying transformers to
     tracked data; `GoodH = Σ T , LT × ∀ w BndL` with ground extraction
     `GoodH-ι-to-<ε₀`. Provided: `GoodH-Zero/Succ/Ω` (each base
     combinator's zone pack is a one-chain bound at `(D, c, M, j)` =
     `(Z, Z/ι[1], ω, 0)` — empty accumulators reduce definitionally),
     `GoodH-app` (the maps component does everything), and the **recursor
     bridge `pack-to-Tracked`**: an `ι ⇒ ι` zone pack *is* a `Tracked`
     witness — erase the empty-accumulator noise by `⊕-Z-left` (a genuine
     induction, function extensionality at limits) and fold the budget into
     the multiplier (`bumpk j M`, still `ValidMult`); since `𝕂 ι = GFun =
     𝔻 ι` and `BndH` agrees definitionally with (45)'s `BndD` at `ι ⇒ ι`,
     module 45's orbit engine applies directly to the recursor's argument.
     Remaining: the `K`/`S`/`Iter` packs (each an instantiation of an
     argument's pack + one (50) rebase — for `S`, `PackDom (Fγ b)` supplies
     the rebase's hypotheses exactly, the designed payoff of (48)) and the
     closing `goodμ` over full `T₁` with the height payoffs. The conjecture
     remains open.

(52) `DialogueTreeHeight.MultHereditaryH5` — **Design H, stage 2d(i): the
     good-inputs orbit — the recursor's `GoodT` side over the tower.**
     (39)'s `orbit-good-aff` consumes an inner-affine bound at *all*
     transformers, but the tower's bound relation delivers it only at
     *good* ones — which suffices, since the orbit engine applies the bound
     only to the iterates `iter Tg Ta k`, good by `GoodT-iter`.
     **`orbit-goodT`** is the mirror of `aff-orbit-≤`/`orbit-good-aff` with
     the goodness threaded through the domination induction; and
     **`BndH-to-aff-good`** extracts the good-inputs affine bound from a
     tower argument: instantiate its `BndH` at the self-datum `(T , gT)`
     (whose bound is reflexivity) and dominate through the tracked pack
     (`pack-to-Tracked`), the multiplier `bumpk j M` valid and `< ε₀`.
     Chained, these give: for any tower argument `(Tg , kg , bndg)` and any
     good start, `GoodT ι (Torbit Tg Ta)` — the recursor's transformer-side
     goodness, unconditional. Remaining for the `T₁`-complete theorem: the
     `Iter`/`K`/`S` zone packs and `goodμ` with the height payoffs. The
     conjecture remains open.

(53) `DialogueTreeHeight.MultHereditaryH6` — **Design H, stage 2d(ii): the
     recursor over the Howard tower, `GoodH-Iter` — proved.** The tower
     datum routes an argument pack through module 45's orbit engine
     (`FI3 kg ka kν = dsum (dOrbit (pr₁ kg) (pack-to-Tracked …) ka) kν`),
     so the bound relation `bndHI` *is* `BndD-Iter`, definitionally. The
     new content is the three zone packs: `pack3` (orbit datum plus count,
     one chain), `pack2` (consuming the start; multiplier `bumpk 3 M̂`
     where `M̂` is the argument's tracked multiplier — the orbit raise
     `bump M̂` and the `⊗ ω`-absorptions fit with a bump to spare), and
     `packI` (consuming the argument; budget `3`, and the multiplier
     obligation reduces to the *budget identity* `bumpk 3 M̂ ＝
     bumpk (3 + jg) Mg` via `bumpk-+` — **the recursor costs exactly the
     argument's budget plus three**, the Howard accounting made literal).
     The `GoodT` side chains (52)'s `orbit-goodT` through
     `BndH-to-aff-good`; the maps at each partial application reuse the
     packs at `selfD` starts; the weight-level bound is Design F's
     `orbit-pt` induction verbatim. Remaining for the `T₁`-complete
     theorem: the `K` and `S` packs and `goodμ` with the height payoffs.
     The conjecture remains open.

(54) `DialogueTreeHeight.MultHereditaryHT` — **the iterator-fragment
     fundamental theorem over the Howard tower: unconditional
     `height < ε₀` for `TI` = combinatory System T with
     `Ω / Zero / Succ / Iter / application`.** The tower's end-to-end
     validation: the fragment has arbitrarily nested, oracle-driven ground
     recursion (counts computed by dialogue with the oracle), every
     construct's `GoodH` closure is proved ((51), (53)), and the
     fundamental theorem is a four-line induction with the payoffs
     `μ-<-ε₀`, `height-<-ε₀`, and `dialogue-height-<-ε₀ :
     (t : TI ((ι⇒ι)⇒ι)) → height (⟦ e t ⟧₁ generic) < ε₀` — each recursor
     nesting costing three bumps over its argument's budget ((53)'s budget
     identity), the heights climbing exactly the `ω`-exponent tower below
     `ε₀`. Honest scope: `TI` omits `K` and `S`, whose tower packs (a
     `reflect` + rebase; the `PackDom`-driven diagonal rebase) are the two
     remaining constructions for the `T₁`-complete theorem — machinery
     (48)–(50) proven and waiting. The conjecture for full System T
     (higher-type recursion) remains open.

(55) `DialogueTreeHeight.MultHereditaryH7` — **Design H, stage 2d(iii): the
     `K` combinator over the Howard tower, `GoodH-K`, fully polymorphic.**
     The constant function's datum reflects its argument (`reflect` — at
     ground the self-datum, at arrows the datum its `LT` carries), and the
     packs are rebase instantiations: `ccore` (the constant map under the
     pack built from the argument's own zone data `kD`/`kM`/`kJ`, rebased
     at `u = ja , e = 0` — concluding budget *equal* to the pack budget
     `rbb (σ₁⇒σ₂) ja 0`) and `ocore-ι`/`ocore-fn` (the argument under the
     outer trivial pack `(Z , Z , ω , rbb σ 0 0)`, its contributions in the
     accumulators, rebased at `u = e = 0` — concluding budget exactly the
     outer budget). The bookkeeping runs on the `u`-independent split
     constant `rbc` with `rbb-＝ : rbb τ u e ＝ u + rbc τ e`, giving
     `rbb σ ja 0 ＝ rbb σ 0 0 + ja` by commutativity — **`K` is
     budget-neutral**: the argument's budget flows through the accumulator
     unchanged. (Also here: `bumpk-pad-left`, `ktail-ι`/`ktail-fn` —
     consuming and forgetting the `τ`-argument by cases, since `with` on a
     parent-clause variable is not available.) Remaining for the
     `T₁`-complete theorem: `GoodH-S` and the closing `goodμ` with the
     height payoffs. The conjecture remains open.

(56) `DialogueTreeHeight.MultHereditaryH8` — **Design H, stage 2d(iv): the
     `S`-diagonal pack core, verified.** `GoodH-S`'s data map is the
     diagonal `Fδ ka = pr₁ (pr₁ kφ ka) (pr₁ kγ ka)`; this module builds and
     verifies its pack `packδ` for a ground shared argument (`ρ = ι`) and
     ground middle (`σ = ι`), any result `τ`. Consuming the shared argument
     in `φ`'s pack yields (its second slot) a `ZApply` that, fed the γ-value
     `Fγ ka`, produces the "raw" diagonal `ZCont` with the γ-value in the
     accumulator; `γ`'s own pack (at `ka`) bounds it, and one `ZCont-rebase`
     folds it in — I1 a heterogeneous quadruple absorption (`quad4`), the
     γ-zone a triple (`trip3r`). **The build validates the budget resolution
     that dissolves the earlier paper tension: `packδ` is constructed with
     both `kφ` and `kγ` in scope, so `γ`'s budget rides in the *multiplier*
     (`Bγ = bumpk jγ Mγ`, inside `Mδ = bumpk 3 (Mφ ⊗ (Bγ ⊗ ω))`), while the
     diagonal's *budget* `jδ = rbb τ jφ 0` depends only on `jφ` — the rebase
     runs at `u = jφ , e = 0`.** So the `S` mechanism over the tower is
     verified at its core; the fn-middle case (`σ` an arrow, γ-value fed to
     `φ`'s slot as a function, its `PackDom` supplying the rebase
     hypotheses) and the outer packs (`pack2`, `packS`) reuse this same
     rebase pattern, and are the remaining constructions for the full
     `GoodH-S`. The conjecture remains open.

(57) `DialogueTreeHeight.MultHereditaryH9` — **Design H, stage 2d(v): the
     outer-pack multiplier-absorption lemma, verified.** The outer packs
     `pack2`/`packS` of `GoodH-S` must dominate the diagonal's multiplier
     `Mδ = bumpk 3 (Mφ ⊗ (Bγ ⊗ ω))` (which carries the second argument's
     budget inside `Bγ = bumpk n Mγ`) by `bumpk (j₂ + n) pool`, with `pool`
     containing `Mφ`, `Mγ`, `ω`. **`mult-absorb`** proves exactly this:
     flooding everything below `pool` makes the base `P ⊗ (P ⊗ P)` with
     `P = bumpk n pool`, absorbed by two `⊗-≤-bump` steps (`⊗³-≤-bumpk2`)
     into `bumpk 2 P`, and the outer `bumpk 3` composes (`bumpk-+`) to
     `bumpk 5 P = bumpk (5 +ℕ n) pool`. So the outer packs cost a *fixed
     five bumps* over the consumed argument's budget — the one genuinely
     multiplicative obligation of the outer `S` packs closes with `j₂ ≥ 5`;
     the zone and budget clauses are routine increasing-chains and
     `bumpk-pad`. Combined with (56)'s verified diagonal core, the `S`
     construction over the tower is de-risked end to end: what remains is
     the systematic assembly of `pack2`, `packS` and `goodμ` from these
     verified pieces. The conjecture remains open.

(58) `DialogueTreeHeight.MultHereditaryHTK` — **the `K`-extended
     iterator-fragment fundamental theorem: unconditional `height < ε₀` for
     `TK` = combinatory System T with `Ω / Zero / Succ / Iter / K /
     application`.** Strictly extends (54)'s `TI` with the constant
     combinator, now that `GoodH-K` (55) is proved fully polymorphic; the
     theorem is a short induction over the six proven `GoodH` closures, with
     payoffs `μ-<-ε₀`, `height-<-ε₀`, `dialogue-height-<-ε₀`. Honest scope:
     `TK` omits `S` — its tower packs (the verified diagonal core (56) and
     outer-multiplier absorption (57), plus the remaining
     `pack2`/`packS`/assembly) are the last construction for the
     `T₁`-complete theorem. The conjecture for full System T remains open.

(59) `DialogueTreeHeight.MultHereditaryH10` — **Design H, stage 2d(vi): the
     `bumpk`-index monotonicity toolkit.** Every `PackDom` obligation of the
     outer `S` packs (`pack2`, `packS`), after the verified multiplicative
     step (57) and the zone/budget increasing-chains, reduces to a
     `bumpk`-index inequality `bumpk a P ≤ bumpk b P` for naturals `a ≤ b`
     built from `_+ℕ_` of argument budgets and constants. This isolates that
     bookkeeping as a small order-theory of `le a b = Σ d , b ＝ a +ℕ d`:
     `le-refl`, `le-trans`, `le-add-right`/`le-add-left`, the commuting
     `le-+ℕ-right`/`le-+ℕ-left` (carrying an argument budget as a tail
     through the pack indices), `le-＝-left`/`le-＝-right` (rewriting an
     index along an `_+ℕ_` identity, e.g. erasing `+ℕ 0`), and the bridge
     `bumpk-le : le a b → bumpk a P ≤ bumpk b P` (via `bumpk-pad`). With
     (56), (57) and this, every sub-component of the outer `S` packs is
     verified; the `pack2`/`packS` assembly is their mechanical composition
     (the choices — `D₂ = Dφ`, `c₂ = cφ`, `M₂ = Mφ ⊗ ω`,
     `j₂ = rbb ι ((jφ +ℕ 0) +ℕ 5) 0`, rebase at `u = (jφ +ℕ 0) +ℕ 5, e = 0`
     — are recorded in the project memory). The conjecture remains open.

(60) `DialogueTreeHeight.MultHereditaryH11` — **Design H, stage 2d(vii):
     the jγ-free-multiplier diagonal absorption — the inequality that lets
     the `S`-diagonal pack *compose*.** Working through `pack2` revealed
     that (56)'s `packδ`, though it compiles in isolation, parks the second
     argument's budget in its *multiplier* `Mδ`, which then cannot pass the
     outer rebase's pool hypothesis `I2` (no `+JH` slot) with fixed slack —
     a genuine interface flaw, not transcription. The resolution routes that
     budget through the *budget* instead (`uδ = jγ +ℕ (jφ +ℕ 3)`), keeping
     `Mδ = bumpk 3 (Mφ ⊗ (Mγ ⊗ ω))` **jγ-free**; then `pack2`'s `I2` is
     `mult-absorb` at `n = 0` (constant slack `5`, already verified), and
     the diagonal's `I1` needs — in place of the old `keyM` — the bound
     **`diag-absorb`** verified here: `((ω ⊗ bumpk n (Mγ ⊕ Z)) ⊗ ω) ≤
     bumpk (2 +ℕ n) (Mφ ⊗ (Mγ ⊗ ω))`. The `bumpk n (Mγ ⊕ Z)` is the
     γ-value's multiplier (`n = jγ`, forced by γ's pack); this absorbs it
     and the two `ω` factors into `2 + n` bumps of the jγ-free base, carried
     by the diagonal's budget index. So the sole new inequality of the
     budget-routing resolution is machine-checked; with it, `mult-absorb`,
     and the (59) index toolkit, every arithmetic obligation of the
     corrected (jγ-free) `packδ` and its composition into `pack2` is
     verified. Rebuilding (56) to the jγ-free design and assembling
     `pack2`/`packS`/`goodμ` is the remaining transcription. The conjecture
     remains open.

(61) `DialogueTreeHeight.MultHereditaryH12` — **the arithmetic obligations
     of `pack2`, verified in isolation.** Assembling the middle `S` pack
     requires several `bumpk`-index / `rbb`-budget identities mixing the two
     argument budgets `jφ , jγ` with constants — the error-prone core. This
     module discharges them as standalone lemmas against the (59) `le`
     toolkit, with the clean fixed budget `j₂ = 9 +ℕ jφ`: `eq-j2`
     (`rbb ι (3 +ℕ jφ) 5 ＝ j₂`, matching the inner `ZCont-rebase` output),
     `jδ-＝` (`rbb ι ((2 +ℕ jγ) +ℕ jφ) 0 ＝ (3 +ℕ jφ) +ℕ jγ` — commuting the
     argument budgets through the successor), and the pack obligations
     `L-pm` (multiplier), `L-pj` (budget `PackDom`), `L-I3z` (inner-rebase
     budget), `L-I1z` (inner-rebase multiplier index). With the jγ-free
     `packδ` (56), the pool absorption (57), and these, every non-plumbing
     obligation of `pack2` is verified; the remaining work is the `pack2`
     structure (`PackDom` triple + a `ZCont-rebase` of `packδ`'s body at the
     constant slack `e = 5`) threading these checked pieces, then `packS`,
     `GoodH-S`, `goodμ`. The conjecture remains open.

(62) `DialogueTreeHeight.MultHereditaryH13` — **`pack2` — the middle pack of
     the `S` combinator over the tower (`ρ = σ = τ = ι`), assembled and
     verified.** Consuming the second argument `kγ`, `pack2` produces the
     zone pack of the jγ-free diagonal `kδ = (Fδ , packδ)` (56). The
     `PackDom` triple threads the verified arithmetic ((61) `L-pm`/`L-pj`,
     (57) `mult-absorb` at `n = 0`) with quadruple zone absorption; the
     inner `ZApply` rebases `packδ`'s body by one `ZCont-rebase` at the
     **constant** slack `e = 5` — the payoff of the jγ-free multiplier —
     with `I1` a five-fold absorption (`pent5` = a quadruple plus one
     duplication) and `I3`/multiplier discharged by `L-I3z`/`L-I1z`/
     `mult-absorb`. Output budget `j₂ = rbb ι (3 +ℕ jφ) 5` matches the
     rebase output definitionally, converted to `9 +ℕ jφ` (where the `(61)`
     lemmas live) by `eq-j2`. The interface-flaw resolution is thereby
     realised end to end: the once-blocking outer `S` pack now closes
     because `Mδ` is jγ-free and the rebase slack is constant. Remaining for
     the `T₁`-complete theorem: `packS` (same pattern one level up,
     consuming the function-typed `kφ`), then `GoodH-S` and `goodμ`. The
     conjecture remains open.

(63) `DialogueTreeHeight.MultHereditaryH14` — **`packS` — the outer pack of
     the `S` combinator, assembled and verified.** Consuming the
     function-typed first argument `kφ`, `packS` produces the zone pack of
     `FS kφ = (F2 kφ , pack2 kφ)` (62); the inner `ZApply` rebases `pack2`'s
     body by one `ZCont-rebase` **at the arrow type `ι ⇒ ι`** (the lemma
     propagates the four leaf invariants through the arrow) at the constant
     parameters `u = 9 , e = 2`, so `jS = rbb (ι⇒ι) 9 2` is the literal
     constant `13`. `PackDom` dominates `kφ`'s partial-application data; `I2`
     is a two-bump pool absorption, `I1` a quadruple leaf absorption, `I3`
     the `eq-j2`-converted budget `le`. All three packs (`packδ`, `pack2`,
     `packS`) are now verified.

(64) `DialogueTreeHeight.MultHereditaryH15` — **`GoodH-S` and the fundamental
     theorem for the fragment `TS` = `Ω/Zero/Succ/Iter/K/S/·` — all seven
     combinators over the Howard tower.** With `kS = (FS , packS)` in hand,
     `GoodH-S` assembles: the transformer is Design F's
     `λ Tφ Tγ Ta → Tφ Ta (Tγ Ta)`; the `LT` maps thread the argument data,
     carrying the tower data `FS kφ` / `F2 kφ kγ` (the diagonal) at each
     partial application; and — the payoff of the whole tower construction —
     the `BndH` component closes in **one line** from the arguments' `BndH`s,
     because the diagonal `Fδ ka = pr₁ (pr₁ kφ ka) (pr₁ kγ ka)` is exactly the
     composition the bound relation feeds; the `BndL` is Design F's `Good-S`
     verbatim. The fragment `TS` (with `S` at `ρ = σ = τ = ι`) then has
     `goodμ`, `μ-<-ε₀`, `height-<-ε₀`, and the unconditional
     `dialogue-height-<-ε₀ : (t : TS ((ι⇒ι)⇒ι)) → height (⟦ e t ⟧₁ generic)
     < ε₀`. Honest scope: this is the *all-ground* `S`; higher-`σ`/`τ` `S`
     (the joint-data instances of `T₃` on the Design-F line) is not yet
     ported to the tower, so `TS` is not yet full `T₁`. The conjecture for
     full System T remains open.

(65) `DialogueTreeHeight.MultHereditaryH16` — **the function-middle `I2`
     absorption — the new arithmetic of the `S`-diagonal at a function-typed
     middle `σ`, the tower's unique target.** At a ground middle (56) the
     γ-value is a `GFun` bounded by a single `⊗ Bγ` term; at a *function*
     middle it is a `𝕂 σ` whose *multiplier* enters the pool, bounded via
     γ's `PackDom` by `bumpk jγ Mγ`. `fnmid-I2` verifies that the diagonal's
     rebase `I2` absorbs `Mφ ⊕ (that multiplier)` into the jγ-free
     `Mδ = bumpk 3 (Mφ ⊗ (Mγ ⊗ ω))` at budget cost `jγ + 2` (rebase slack
     `e`), keeping `Mδ` jγ-free so the outer packs stay at constant slack.
     This is the first verified piece of the function-middle diagonal — the
     case Design F provably cannot reach and the reason the whole tower
     exists. Remaining: the `σ = arrow` diagonal pack (`I1` reusing
     `diag-absorb`, `I2` this lemma, `I3` γ's `PackDom` budget bound), then
     the generalized `pack2`/`packS` and a function-middle `GoodH-S`. The
     conjecture remains open.

(66) `DialogueTreeHeight.MultHereditaryH17` — **the `S`-diagonal pack at a
     function-typed middle `σ = σ₁ ⇒ σ₂` — the case Design F cannot reach,
     the Howard tower's purpose, verified.** At a function middle the
     γ-value fed to `φ`'s slot is a `𝕂 (σ₁ ⇒ σ₂)`, fed via the `ZApply`
     *arrow* clause, and its additive/multiplier/budget data enter the
     diagonal's accumulators — bounded by **γ's own `PackDom`** (the tower
     predicate's constraining clause), which supplies the three rebase
     hypotheses: `I1` (`kadd`γ ≤ `⊗ Bγ`, same shape as the ground γ-value,
     so `I1` reuses `quad4` + `diag-absorb`), `I2` (`kmult`γ ≤ `bumpk jγ
     Mγ`, absorbed by (65)'s `fnmid-I2`), `I3` (`kbudget`γ dominated by
     `jγ`, threaded through `bumpk-+`). `Mδ = bumpk 3 (Mφ ⊗ (Mγ ⊗ ω))` stays
     **jγ-free**; the argument budgets ride in `uδ = jφ +ℕ jγ`,
     `eδ = jγ +ℕ 2`. `Sδ-fnmid.packδ` builds the diagonal for any
     `σ₁ σ₂ τ` — **this is the first machine-checked piece of `S` that
     exceeds Design F's reach.** Remaining: generalize `pack2`/`packS` to
     consume the function-middle diagonal, then a function-middle
     `GoodH-S`. The conjecture remains open.
