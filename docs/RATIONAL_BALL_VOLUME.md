# Rational ball volume: capability boundary

## Chapter 2: persistent positive-orthant computation (2026-10-09)

The sphere example now uses one rational positive-orthant chart, the same dyadic
subdivision for every parameter, and recursive coordinate-face charts. The
inner hull includes the origin. Every sampled tangent plane is retained,
including the positive axis tangents; coordinate planes complete the outer body.

`OrthantBallComputation` retains its samples, facets, and rational endpoints.
Initialization computes the axis-simplex and unit-cube volumes. Later stages
add only visible-facet pyramid volumes to the inner endpoint and subtract only
clipping-cap volumes from the outer endpoint. The 3D facets are updated locally.
The factor \(2^n\) uses standard ambient orientation on every reflected piece.
`ConvexPolytope.volume()` applies only to finite rational polytopes. No general
volume for regions bounded by surfaces, or preassigned sphere volume, is used.

The exact tests guard against whole-body volume calls during refinement and
compare with independent polytope computations. Saved certificates verify five
3D stages, \(228\) point updates and \(3108\) positive determinant simplices.
Native Lean checks \(14\) chart, positive-orthant, power and shell statements.
The isolated rational Mathlib package checks another \(24\) statements,
including origin membership, orthant containments, refinement and axis bounds.
Actual theorem dependencies exclude Mathlib real/complex scalars, measure and
integration; broad Mathlib module imports remain isolated from the foundation.

**Capability boundary:** the executable finite geometry and interval evaluator
are implemented and checked by exact runtime tests. The full Lean proof of
simplex volume from axioms, triangulation independence, horizon-pyramid and
clipping-cap dissections, chart coverage and quantitative gaps, and agreement
of a valid represented interval computation with the general-dimensional
formula remains unfinished. The chapter gives the separate mathematical
formula-agreement argument; it does not adopt a general curved-region volume
operator or assume that agreement as a certificate field.
