
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
