# Rational ball volume: capability boundary

## Chapter 2: rational ball geometry and volume (2026-10-09)

The chapter now gives a general-dimensional finite-dissection proof of
\(v_{n+2}=2\pi v_n/(n+2)\), using rational boundary samples and exact
inner/outer polytope volumes. The simplex formula is derived mathematically
from finite additivity, positivity in the standard orientation, translation
and determinant-one invariance, and unit-cube normalization. Its orientation
convention is \(\det(p_1-p_0,\ldots,p_n-p_0)/n!\).

`ComputableAnalysis/FiniteRationalBall.lean` checks twelve finite rational
chart, power, partition, and shell identities, using native Lean only.
`book/rational-nball` contains the chapter addition, exact 3D certificates,
reader assets, source hashes, axiom audits, and reproduction instructions.
An isolated package at Mathlib revision
`51e6992efd06126df61a496bebf8f49482a4e129` checks convex bodies on
`Fin n → ℚ`, rational halfspaces, refinement and boundedness, and rational
determinant identities. The transitive proof-declaration audit excludes
Mathlib real/complex scalars, measure, and integration. The broad Mathlib
module import closure is not joined to the native foundation.

**Capability boundary:** these are checked finite arithmetic, convexity,
and linear-algebra statements. The simplex-from-axioms proof, triangulation
independence, chart net coverage, quantitative polytope gap, product volume,
and agreement with a valid represented ball volume remain Lean obligations.
The earlier `FiniteNBallVolume.lean` is an algebraic formula model, not this
missing geometric bridge. A complete geometric Lean theorem is not claimed.
