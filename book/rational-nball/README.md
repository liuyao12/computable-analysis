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

## Checked rational volume foundation (2026-10-10)

`RationalPolytopeVolume.lean` states the supplied volume axioms, retaining determinant-one invariance, and proves rational cube subdivision and dilation. `RationalSimplexGeometry.lean` verifies the staircase dissection of the cube and standard simplex normalization. `RationalSimplexDissection.lean` proves edge-cut dissection and positive rational stretch scaling. `RationalSimplexVolume.lean` proves the determinant formula in every dimension, including degenerate and negative orientations, and the induced dilation law for every rational factor. It proves independence for supplied positive triangulations with geometric dissection evidence. A general triangulation constructor and the full sphere convergence/agreement proof remain unfinished.

Run `lake build RationalGeometry` in the isolated proof package. The final module audits actual declaration dependencies and uses `Lean.collectAxioms` to reject every axiom except `propext`, `Classical.choice`, and `Quot.sound`.

## Finite Archimedes recurrence proof (2026-10-10)

Extract `native-archimedes-proof.tar.gz` into an empty directory, then run:

```sh
lean -o ComputableAnalysis/FiniteNBallVolume.olean ComputableAnalysis/FiniteNBallVolume.lean
lean -o FiniteRationalBall.olean FiniteRationalBall.lean
LEAN_PATH=. lean -o FiniteBallShellRecurrence.olean FiniteBallShellRecurrence.lean
LEAN_PATH=. lean -o FiniteBallFormulaInduction.olean FiniteBallFormulaInduction.lean
LEAN_PATH=. lean CheckArchimedes.lean
```

This package needs only the pinned Lean toolchain; it uses no Mathlib or Basic represented-real dependency. The recurrence estimates and even/odd induction are checked in every dimension. They are intermediate results: the geometric polytope shell-product comparison and represented sphere formula agreement remain unfinished. `RationalDissectionTransform.lean` checks rational transport of geometric dissections and derives product volume for positive rational boxes.

## Rational polytope clipping and dissection (2026-10-10)

`RationalPolytopeCuts.lean` constructs rational clipping vertices from retained
vertices and all crossing-edge intersections, and proves exactly that their
convex hull is the intersection of the original hull with the cutting
halfspace. A barycentric redistribution proof covers empty and degenerate
cuts. The two halfspace cuts form a proved geometric dissection, so finite
additivity gives retained volume plus cap volume equal to the preceding
volume. Repeated cuts give a proved telescoping cap-subtraction identity.
The tangent-cut specialization applies to every finite list of rational unit
samples in every dimension, including axis samples.

The module also proves finite dissection refinement, coverage and volume
conservation of common cuts, clipping idempotence and commutation in volume,
and nonnegativity from the derived determinant formula for supplied positive
triangulations. No positivity, general determinant scaling, product-volume,
or curved-region-volume axiom has been added. All 18 endpoints pass the
trusted-axiom and rational-scalar dependency audits.

The original Archimedes induction remains unfinished: constructing positive
triangulations of caps and shell products, their product-volume law, the
incremental sphere evaluator in Lean, and its convergence/comparison bridge
are still required. The conditional represented-real recurrence is not being
advertised as an unconditional sphere theorem.
