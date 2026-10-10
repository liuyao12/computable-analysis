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
