# Rational ball volume: capability boundary

## Chapter 2: finite Archimedes recurrence estimates (2026-10-10)

The disk computation defines \(\pi=v_2\). The intended geometric recurrence
is \(v_{n+2}=2\pi v_n/(n+2)\), whose \(n=1\) instance is Archimedes' sphere
argument. New native Lean proofs verify the finite shell–disk coordinate
containments and a quantitative shell estimate for every positive dimension.
For any normalized rational partition of mesh \(d\), its coefficients satisfy
\[
\frac{2}{n+2}-2d\le A\le\frac{2}{n+2}+d,
\qquad A\le B\le\frac{2}{n+2}+3d.
\]
An explicit uniform partition supplies \(d=1/N\). Separate finite induction
solves the recurrence model in every even and odd dimension, yielding the
factorial formulas. This proves the model's algebra; it does not identify it
with the sphere's polytope computation.

The rational geometry layer also constructs the transport of finite
polytope dissections under invertible rational maps, derives determinant
scaling for verified positive triangulations, and proves product volume for
positive rational boxes from the existing volume axioms. No product-volume
axiom, integral, Gamma function, or general curved-region volume is added.
There are now \(72\) checked endpoints. The native Archimedes package requires
only the pinned Lean toolchain, with a trusted-axiom audit. The finite
recurrence model's unnecessary Basic dependency is removed.

**Remaining bridge:** general polytope products, the finite shell-product
volume comparison for the actual sphere polytopes, their quantitative
coverage and convergence, and exact agreement of the valid represented
sphere computation with the formula. The geometric recurrence and full
general-dimensional sphere theorem are still unfinished.

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
