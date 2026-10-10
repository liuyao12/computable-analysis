# Rational ball volume: capability boundary

## Chapter 2: rational simplex volume from the axioms (2026-10-10)

Determinant-one invariance remains an explicit volume axiom, as requested.
The isolated rational Mathlib package now verifies the actual rational cube
grid dissection, cube normalization and rational dilation, the cube staircase
dissection into \(n!\) simplices, and the rational edge-cut dissection. These
prove the determinant formula for every ordered rational simplex in every
finite dimension, including degenerate and reversed orientations. The simplex
dilation theorem covers every rational factor \(k\), with factor \(k^n\).
No integral, Gamma function, or general curved-region volume is introduced.

For supplied positive triangulations with proved geometric coverage and flat
pairwise intersections, determinant sums compute the axiomatic volume and are
independent of triangulation. This theorem does not construct a triangulation
for an arbitrary rational polytope. The package contains \(55\) checked
endpoints. Its actual declaration dependencies exclude Mathlib real/complex
scalars, measure, and integration. The new combined audit additionally uses
`Lean.collectAxioms` to reject untrusted axioms and placeholders.

**Remaining work:** the general triangulation constructor, the incremental
visible-pyramid and clipping-cap dissections, chart-grid coverage, quantitative
containment and convergence, product-volume comparisons, and agreement of the
valid represented sphere computation with the general-dimensional formula.
The complete general-dimensional sphere proof is still unfinished.
