# Chapter 2: a stateful rational sphere computation

Only finite rational convex polytopes have a `volume()` function here. There is
no general definition of volume for regions bounded by surfaces, and no sphere
volume is assumed before this particular interval computation. Agreement with
the general-dimensional formula is a separate mathematical argument in
`chapter-section.html`; its full geometric Lean bridge remains unfinished.

## Persistent evaluator

```python
from orthant_ball import OrthantBallComputation
computation = OrthantBallComputation(3)
initial_bounds = computation.bounds()
computation.refine()
refined_bounds = computation.bounds()
```

Initialization uses the axis simplex and unit cube in the positive orthant.
All positive axis tangent planes and all coordinate planes are retained.
Each refinement doubles the shared parameter-grid denominator, evaluates
only newly introduced grid tuples and coordinate-face tuples, and deduplicates
against the retained sample set. The inner hull grows by visible-facet pyramids;
the outer body is clipped by each new tangent and loses the corresponding cap.
Cached rational endpoints are updated by addition and subtraction of the local
pieces. Neither whole-body volume is recomputed during refinement.

In three dimensions, the existing facet polygons are updated along the horizon
and clipped directly. The algorithms also accept other finite dimensions,
where exact facet enumeration can become expensive. Recursive coordinate-face
sampling prevents permanently coarse flat faces of the inner hull.

`rational_polytopes.py` provides the common rational vertex/halfspace type,
triangulation, and `ConvexPolytope.volume()`. The default ambient orientation
orders every emitted simplex positively. `volume(-1)` reverses the body
orientation. `simplex_volume(ordered_vertices)` retains the specified vertex
orientation and can be negative. Floating-point coordinate inputs are rejected.
A halfspace presentation requires a supplied strict rational interior point;
the polar hull certifies boundedness, and unbounded inputs raise an exception.

## Exact runtime checks

```sh
python3 -m unittest -v test_rational_polytopes
python3 generate_polyhedra.py
python3 check_polyhedra.py
```

The generator uses the persistent evaluator. Its saved certificates include
every point update, positive determinant pyramid and cap simplices, endpoint
increments, and current meshes. The independent checker recomputes volumes from
saved polytope vertices, verifies local cap triangulations, and checks the exact
endpoint ledger. This verification is separate from the stage algorithm.
`runtime-tests.txt` and `certificate-check.txt` record the checks.

Tests cover cubes through dimension four, orientation reversal, rational affine
maps, degenerate bodies, coplanar/collinear/duplicate points, bounded and unbounded
halfspace presentations, a reference supporting-plane enumeration, recursive
face grids, and equality of incremental endpoints with independent polytope
volumes. A guarded-volume test rejects whole-body volume calls during refinement.
`polyhedra.json` stores exact rationals. `polyhedra-data.js` uses rounded vertices
only for rendering and outward-rounded displayed numerical endpoints.

## Native Lean arithmetic

```sh
lean -o FiniteRationalBall.olean FiniteRationalBall.lean
LEAN_PATH=. lean CheckFiniteRationalBall.lean
```

Fourteen native endpoints check the rational chart and its positive-orthant
property, finite power/partition estimates, and shell identities. Their axiom
audit uses only standard Lean axioms, without admissions.

## Isolated rational Mathlib layer

Download and extract `rational-geometry-proof.tar.gz`, then run:

```sh
lake update
lake exe cache get Mathlib/Analysis/Convex/Hull.lean Mathlib/Tactic/Linarith.lean Mathlib/LinearAlgebra/Matrix/ToLin.lean
lake build
lake env lean RationalOrthantBodies.lean
```

Mathlib is pinned to `51e6992efd06126df61a496bebf8f49482a4e129`.
`RationalOrthantBodies.lean` checks origin membership, convexity, inner/outer
containment, refinement, and boundedness from the retained axis tangents on
`Fin n → ℚ`. The package also preserves the general rational convexity and
determinant-coefficient layers. Audits exclude Mathlib real/complex scalars,
measure, and integration from actual transitive theorem declarations. Broader
module imports do contain real/complex modules, so this package stays isolated
from the native foundation's import closure.

The remaining geometric Lean obligations include simplex volume from the
axioms, triangulation independence, horizon-pyramid and clipping-cap dissection
laws, chart net coverage, quantitative gaps, and agreement of the particular
valid represented interval computation with the formula. Algebraic formula
models and the runtime certificates do not prove these missing bridges.

## Reader maintenance

```sh
python3 apply_chapter_overlay.py /path/to/base/ch-circle-sphere.html ch-circle-sphere.html
```

The overlay is idempotent and preserves the rest of the reader. Publication
updates only this chapter and its assets on the existing Pages destination.
