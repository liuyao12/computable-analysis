
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
