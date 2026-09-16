# A radical evaluation alternative, not a fourth proof

The public convention remains C(x)=cos(pi*x), with x in [0,1/2]. The product
is pi times its integral on that interval, not on [0,1]. A unit-interval
presentation would use c(t)=C(t/2) and the coefficient pi/2.

## Checked native capability

Import `ComputableAnalysis.DyadicCosinePrimitive` for a separately constructed
radical quadrature and the theorem `product_eq_one`. Its `product` is literally
`RealRaw.mul CosinePrimitive.pi DyadicCosineIntegral.integral`, and `Statement`
is its equivalence to the constant-one interval program. Validity is proved
separately by `product_valid`. Pi remains four times geometric arctangent at one.

The closed clock identities prove addition, complement, endpoints and positive
half-angle squares. The numerical radical path starts at slope one and iterates
u/(1+sqrt(1+u*u)), where square roots are rational bisections. Finite rotation
powers supply every dyadic numerator. `dyadic_values` identifies these very
programs with the original closed `CosinePrimitive.S` and `C` at j/(2*2^d).
No cosine-integral endpoint theorem is used to prove that identification.

`DyadicCosineIntegral` retains dyadic meshes, reevaluates their finite radical
sample sets, and intersects boxes widened by 1000/2^d. Its finite-sum agreement
and validity are proved before the endpoint comparison. This is a conservative
checked construction, not the sharper numerical schedule in the illustration.
The product corollary reuses existing calculus results; it is not an independent
fourth derivation of the old common basepoint proposition.

## Numerical illustration

`dyadic_numerics.py` supplies cosine samples solely from nested positive square
roots and reflection. Its pi factor is separately computed by rational chord
and tangent polygons at u=1. Monotone right/left rectangles enclose the integral.
The product is never set to one and the integral is never computed by 1/pi.
The displayed decimal endpoints are rounded outwards. The 72-bit integer-square-
root enclosures and all polygon bounds are rational computations.

This Python program is not extracted Lean code and has not been identified
stage-by-stage with the formal evaluator. Its six finite numerical experiments
are labeled accordingly. Refinement of the underlying exact computations is a
different question from treating a fixed 72-bit display precision as an infinite
valid real-number program.

## A separate bundled proof map

The new page is `dyadic-integral.html`; its theorem map is `thm:dyadic-product`.
The old three proofs, graph SVGs, and benchmark roots are preserved. The new map
has a separate verifiedGraph flag and one checked route, rather than pretending
to be either a three-way comparison or an unverified editorial outline.

Black statement arrows unfold only definitions of the actual statement. Colored
arrows enter a proof or certificate body and carry stored-reference witnesses.
The trigonometric identities justify replacing C by its radical evaluator;
they are not added as artificial hypotheses or definition dependencies of the
old theorem. Graph edge inspectors are scoped to the selected theorem.

## Verification

CI builds the native module and runs `book/checks/ExportDyadicEvaluation.lean`.
It rejects transitive sorryAx, native-owned noncomputable declarations and any
Mathlib dependency in the new roots. A separate definition-body traversal checks
that the radical integral does not reach pi, arctangent or the inverse provider;
proof dependencies on those objects are not numerical calls. This is not a
claim about arbitrary compiler optimizations or a replacement for the full
inherited axiom report. Existing upstream native-computation axioms remain
explicitly reported.

The postprocessor validates every displayed edge, and tests check outward
rounding, square-root intervals, independent numerical factors, preservation
of the earlier graph and metrics, exact Lean cards, and browser interaction.
No protected chapter source is edited.
