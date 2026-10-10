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

## Rational polytope volume monotonicity (2026-10-10)

`RationalVolumeMonotonicity.volume_mono` now proves, for every dimension,
that containment of rational convex polytopes implies the volume inequality.
No positivity or monotonicity axiom, or supplied triangulation certificate,
is needed. The ordered simplex retains its determinant sign; the body in the
fixed ambient orientation has volume \(|\det A|/n!\).

`RationalSimplexEdgeCuts.lean` constructs a rational cutting hyperplane for
an arbitrary crossing edge of a nonsingular simplex and proves an exact
two-simplex dissection. Repeating this reduces the number of vertices off
the original cutting plane. A well-founded induction proves nonnegativity
of a simplex after any finite list of rational cuts. Transporting the cube's
explicit staircase dissection through rational affine maps and cuts proves
nonnegativity for every finite clipping of a bounding cube.

`RationalHalfspaceElimination.lean` gives executable finite rational
Fourier–Motzkin elimination and proves exact existential elimination,
including inconsistent systems and missing upper/lower bounds. Eliminating
barycentric coordinates proves that every finite rational point hull has
an exact finite rational halfspace presentation. For two contained hulls,
cutting their common bounding cube first by the outer hull's constraints
and then by the inner hull's constraints reproduces the inner hull. Every
removed cap has proved nonnegative volume, giving monotonicity. The public
`volume_mono_of_vertex_halfspace_checks` specializes this to finite rational
vertex–halfspace checks.

The actual orthant inner hull and tangent-clipped outer polytope now have
proved ordered volumes, increasing inner volumes, decreasing outer volumes,
and bounds between zero and the unit cube's volume. Axis tangents remain
included. `orthant_cross_volume_le` compares any inner sample set with any
outer sample set. The 40 new declarations pass kernel declaration checks,
standard-axiom guards, and rational-scalar dependency audits. Executable
elimination checks cover a bounded interval, an inconsistent system and a
system with no upper bound.

The Archimedes sphere recurrence is still conditional: the general
polytopal product-volume law, finite annular shell-product dissection and
comparison, quantitative chart coverage, and validity/agreement of the
actual sphere computation remain to be proved. General cap positivity is
now solved without a universal triangulation constructor. No integrals,
Gamma function, Mathlib real/complex scalars, or general curved-region
volume have been introduced.

## Geometric Archimedes recurrence from finite rational polytopes (2026-10-10)

The finite geometric comparison is now proved, rather than supplied as a
hypothesis. `geometric_archimedes_recurrence` proves, for every \(n\ge 1\),
\[
  v_{n+2}\simeq \frac{2\pi}{n+2}v_n,\qquad \pi=v_2,
\]
where \(\simeq\) is `RealRaw.Equiv`. Its inputs are the existing volume
axioms and supplied valid raw exhaustions whose endpoints are the volumes
of the actual rational orthant point hulls and tangent-halfspace polytopes,
scaled by \(2^d\). Axis tangents remain included. There is no shell-volume
inequality or recurrence assumption in the theorem.

The finite proof first derives uniqueness of rational polytope volume from
constructed cuts and the simplex formula. This proves prism, cone, arbitrary
polytope product, and nonnegative rational dilation formulas from the same
axioms. In particular, for an \(n\)-dimensional rational base \(P\),
\[
 V_{n+1}(\operatorname{prism}(P,r))=rV_n(P),\qquad
 V_{n+1}(\operatorname{cone}(P))=\frac{V_n(P)}{n+1}.
\]
The cylinder-minus-cone remainder is an actual incremental list of rational
caps, with total volume \(nV_n(P)/(n+1)\). In three dimensions this is the
finite half-cylinder comparison, giving the full sphere coefficient
\(4\pi/3\) once \(v_1=2\) is used.

Finite-family comparison is also derived: a covered convex polytope has
volume at most the sum of the covering polytope volumes, and a family
contained in a convex polytope with only flat overlaps has sum of volumes
at most its volume. The proof cuts all polytopes by the same finite rational
hyperplanes and uses vertex averages to verify each resulting cell.
Neither assertion is a new volume axiom.

For a radial cell \([a,b]\), lower shell pieces are the caps incrementally
removed from \(bP\) by the scaled tangent planes of \(aQ\). Each cap satisfies
\(a^2\le\|x\|^2\le b^2\), and its product with a rationally scaled disk
polytope fits inside the next ball's outer polytope. Different radial cells
have only flat overlaps. Upper shell pieces are the caps removed from
\(bQ\) by the halfspaces of \(aP\); products with rational upper disk bounds
cover the next ball's inner polytope. The zero-prefix slice is flat and
has zero volume. Thus no volume is assigned to a curved shell or annulus.

The already-checked finite power sums give coefficients within \(3/N\) of
\(2/(n+2)\). A finite rational square grid supplies disk radii. Refining the
\(n\)-dimensional bracket until its width is at most \(1/N^2\) gives the
actual orthant polytope comparisons with errors \(6/N\) and \(4/N\).
Validity and nesting then yield the exact raw equivalence above. Internal
partitions and precision choices do not appear in the public recurrence.

The isolated Lean package checks 94 new declarations, rejects nonstandard
axioms, and audits dependencies to exclude Mathlib real/complex scalars,
measure and integration. The proof of product validity replaces one
`native_decide` check of a fixed rational constant by kernel `decide`.
The package includes the public native foundation plus that scoped change.

This completes the geometric recurrence for supplied valid polytopal
exhaustions. It does not construct or prove validity of a new general-dimensional
boundary-sampling evaluator. Quantitative chart coverage and the Lean
validation of the runtime's incremental horizon-pyramid constructor remain
separate obligations. No integral, Gamma function, or general volume of a
region bounded by surfaces is introduced.
