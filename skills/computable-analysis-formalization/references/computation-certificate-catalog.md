# Computation certificate catalog

## Raw numbers and implementation agreement

Use `ComputableAnalysis.Basic` for `QInterval`, `RealRaw`,
`RealRaw.Valid`, and `RealRaw.Equiv`. Define an evaluator as rational boxes.
Prove endpoint order, nesting or an explicit stabilization route, and a
width modulus. Compare two definitions only after both have validity proofs.
Use overlap-based `RealRaw.Equiv`; never use a completed-real quotient as a
shortcut.

## Interval functions and domains

Use `FunctionOnInterval` for a rational closed domain. Start exact polynomial
or affine examples with `FunctionOnInterval.exactRat`. For a quotient, use
`RatFun` and prove `RatFun.DenominatorApartOnInterval`; pointwise
definedness does not exclude an irrational zero of a denominator.

Use `IntervalRegularOn` when a downstream theorem needs a genuine interval
enclosure or rational epsilon-delta continuity. Its
`epsilonDeltaContinuous` theorem is the project route to continuity without
an imported topology.

## Finite derivatives and endpoint formulas

The target for a requested derivative identity is an exact theorem over valid
represented real inputs, using `RealRaw.Equiv` and the genuine mathematical
domain. The finite certificates below support that proof. Prove any missing
real-input evaluation and representation-invariance bridges; do not treat
formal differentiation or a rational-input certificate as the completed
real-input theorem. Internal charts and monotonicity breaks should be resolved
inside the proof. See the [governing policy](../../../FORMALIZATION_GUIDE.md#computable-foundations-exact-mathematical-theorems).

Use `HasDerivativeOnInterval` or `HasForwardDerivativeAt` for rational
finite-difference certificates. Let evaluator precision depend on the
rational step when necessary. Keep a coefficient identity for a formal power
series distinct from an analytic derivative theorem for the corresponding
boxed function.

For a definite-integral identity from a checked derivative formula, use
`EffectiveDerivativeBoundFTC`, then
`FunctionOnInterval.ofRealFunRaw` and
`Integral.effectiveFTCConstructionFor`.  The public endpoint theorem is
`Integral.effectiveFTCIntegral_equiv_endpointDifference`.  Use
`Integral.DefiniteIdentityFor` or a dedicated finite comparison when a
different construction already exists. Certify the whole integration segment,
including pole avoidance and valid branches, and state the result with an
explicit base point and endpoint difference. Do not introduce a separate
primitive notion; see the [definite-integral convention](../../../FORMALIZATION_GUIDE.md#state-integration-formulas-as-definite-integrals).

## Series, exponential, and logarithm

Use `PowerSeries`, `Series`, and `ExpProofs` for a finite prefix plus a
rational tail majorant. State a rate in terms of the public raw evaluator.
Use raw-real equivalence to relate series, Euler products, or other
representations. Do not claim the scalar function identity or derivative
law for an elementary function until the matching interval-function
certificate is present.

Use `ElementaryFunctions` for positive-base and rational-power interfaces.
Retain the explicit obligation of rational-exponent continuity unless the
particular proof supplies it.

## Inverse and algebraic branches

Use `Extension` and `AlgebraicFunctions` for monotone inverse branches.
Supply range, separation, and bisection data instead of selecting a real
root. Treat square roots, inverse trigonometric branches, and logarithms as
represented computations with branch hypotheses.

## Linear ODEs

Use `PeanoBaker` for sampled systems, chronological products, finite
variation of constants, and finite uniqueness. State the discrete recurrence
first. For a continuous theorem, add component interval integration and an
explicit factorial-tail schedule; the finite core alone does not prove
continuous Picard--Lindelof.

For growth near a singularity, use `LinearGrowth.LinearSolution` (namespace
`LinearODE`). It specifies local ODE residuals on refined rational boxes;
`moderate_growth` proves a polynomial bound from a `1/t` column estimate.
The definition must not contain that growth conclusion. `Fuchs.Growth`
provides the polynomial-coefficient rational-ray application; general
holomorphic adapters and the converse criterion remain separate work.

## Local nonlinear pole charts

`GeometricSeriesCalculus` certifies derivatives of rapidly convergent series
by finite differences of arbitrary raw-box samples. Keep the precision
step-dependent. `CauchyProductEstimate` proves the finite convolution error.
`Painleve.Pole` combines these with a derived Laurent recurrence to prove
regular-factor derivative certificates, a shrinking nonlinear PI residual,
and double-pole bounds for the reconstructed value. The singular-coordinate
derivative adapter and global movable-singularity theorem remain open.

## Pi as an integration suite

Use `PiProofs.PiCoverageBridge` only to register an end-to-end independent
bridge. Present normal mathematics in the blueprint: an integral evaluation,
a series theorem, or a geometric formula. Treat Pi agreement as a regression
test for distinct capability families, not as the overall calculus score.

## Required publication record

Update the source module, `blueprint/lean_decls`, a natural-language
blueprint chapter, `GOALS.md`, and `FORMALIZATION_GUIDE.md` when a new
checked public capability is added. State an actual convergence-rate theorem
where the construction has one. Run the no-import/no-placeholder audit before
publishing.

## Arithmetic differential equations

For a generating function such as Apéry's, start with an independent finite
integer construction, then prove its recurrence by finite telescoping.
`Apery` connects that arithmetic proof to an independently defined Euler
operator, ordinary derivative certificates, and an explicit boxed ODE
residual. The monomial-prefix alignment in `shift_prefix` avoids passing to
an unspecified limit. The companion's discrete Wronskian supplies strict
separation, but identifying its approximants with an existing special-function
computation and proving irrationality require further theorems.

## Real zeta above one

`ZetaReal.zeta` is a concrete constructor on represented real inputs with a
finite `AboveOne` certificate. Route real input through the existing adaptive
interval-function application. Its rational core uses two finite cutoffs:
binomial degree and Dirichlet index. `rectangle_outer_tail` and
`rectangle_inner_tail` certify those errors; `dirichlet_convergence` connects
the valid finite sums with the output. `zeta_integer_equiv` is the independent
integer compatibility theorem. This route does not consume an assumed
rational-power extension interface. The separate log–exp bridge remains open.


## Basel and finite Euler products

Import `ComputableAnalysis.Basel.RealZeta` for the proved Basel identity and its
compatibility with the public real-input zeta function. `Basel.FiniteSums`
supplies finite triangular/square reindexing and alternating bounds;
`Basel.ZetaEstimate` supplies the explicit reciprocal-square/Leibniz budget.
`Basel.EulerSieve` and `Basel.EulerBounds` give finite prime sieving and its error
bound. `Basel.Primes` derives prime unboundedness from irrationality of
$\pi^2$ through this sieve. Retain that irrationality hypothesis until it is
proved; do not replace this route with the existing Euclidean infinitude theorem.
Run `scripts/check_basel.lean` to check the elaborated dependency separation.


## Polygonal complex contours

Use `ComplexAnalysis.Cauchy` for actual midpoint contour computations on
rational triangles and finite triangle collections. `CauchyData` requires
executable refinement/evaluation schedules, shrinking sample boxes, and local
complex-affine approximations; it does not assume a contour identity.
`ComplexAnalysis.Residue` combines regular-part cancellation with the
arctangent-normalized square pole for represented complex residues. The
concrete family is the sum of a simple pole and a quadratic polynomial.
General derivative adapters, arbitrary-partition agreement, punctured-polygon
transport, higher-order residues, and Cauchy value/derivative formulas remain
separate obligations. See `docs/POLYGONAL_CAUCHY.md` before claiming scope.
