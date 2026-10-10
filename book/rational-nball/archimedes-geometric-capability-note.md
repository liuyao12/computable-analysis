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
