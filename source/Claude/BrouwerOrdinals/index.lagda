Brouwer ordinals and their arithmetic.

A self-contained development of the constructive arithmetic of Brouwer
ordinal codes (`Ordinals.BrouwerCodes`): the syntactic order and addition,
multiplication and `ω`, the fixed-increment orbit engine, the `ε₀`
sub-development (`ω^_`, `tower`, `ε₀`, strict order and its closure
properties), `ω`-polynomials, Cantor normal forms, affine maps and their
orbit bounds, valid multipliers, and the bump operator.

Everything here is pure ordinal arithmetic — no dependence on dialogue
trees, System T, or the dialogue-tree-height conjecture. It is consumed by,
but does not depend on, `EffectfulForcing.DialogueTreeHeight`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Claude.BrouwerOrdinals.index where

import Claude.BrouwerOrdinals.Order
import Claude.BrouwerOrdinals.Orbit
import Claude.BrouwerOrdinals.Epsilon0
import Claude.BrouwerOrdinals.OmegaPoly
import Claude.BrouwerOrdinals.CNF
import Claude.BrouwerOrdinals.Affine
import Claude.BrouwerOrdinals.AffineClosure
import Claude.BrouwerOrdinals.Affine2
import Claude.BrouwerOrdinals.AffineOrbit
import Claude.BrouwerOrdinals.CNFAffine
import Claude.BrouwerOrdinals.MultAffine
import Claude.BrouwerOrdinals.MultBump
import Claude.BrouwerOrdinals.MultDominated
import Claude.BrouwerOrdinals.MultOrbit
import Claude.BrouwerOrdinals.MultSquareOrbit

\end{code}
