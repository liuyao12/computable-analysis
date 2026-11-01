# Compact reference constructions for agents

These are construction references, not a requirement to imitate one recipe
for every function. Consult the actual Lean statement, its domain, and its
source/build boundary. A finite error estimate, validity proof, and mathematical
identification are different pieces of evidence.

## Dyadic geometric arctangent

**Object and domain.** Compare the geometric sector computation and the
midpoint-refined rectangle value on the checked nonnegative unit branch.
The kernel is rational and decreasing there:

$$
k(t)=\frac1{1+t^2},\qquad 0\le t\le1.
$$

**Construction pattern.** Use exactly the dyadic cell refinement of Chapter 2.
Prove finite rectangle bounds, compatibility of stages, and shrinking from the
squared-mesh estimate. Compare each rectangle bracket with the actual geometric
bracket. No derivative theorem or abstract integral existence is needed for
this finite comparison.

**Existing evidence.** In `ArctanGeometry`, consult
`arctanIntegralRectangle_dyadicSquareMesh`,
`arctanIntegralRectangleRaw_valid`, `arctanGeom_valid_on_unit`, and
`arctanIntegralRectangleRaw_equiv_arctanGeom`.

**Remaining role obligation.** To state a semantic definite-integral theorem,
certify that this actual rectangle computation has the required integral role.
Do not turn a constructor name or a numerical agreement into `HasIntegral`.

## Arctangent inverse and normalized angle

**Object and domain.** The `ArctanInverseConstruction` and `ArctanInverseCircle`
modules provide a particular target-bracket search and circle coordinate
computations. On the justified quarter-turn branch, the target is a rational
multiple of the represented geometric quarter-sector area.

**Construction pattern.** Retain actual rational preimage brackets and
finite evaluation error bounds. Use overlap-safe updates when a target and
an evaluated value cannot yet be separated. Prove the target identity and
the inverse range; neither follows from the output name being valid.

**Existing evidence.** Consult `ArctanInverseCircle.quarterSlope_target`,
`sineQuarter_valid`, and `cosineQuarter_valid`. Their quarter-turn argument
corresponds to the normalized sine and cosine arguments

$$
\sin\left(\frac{\pi t}{2}\right),\qquad
\cos\left(\frac{\pi t}{2}\right).
$$

Use twice the rational argument when defining the first-quadrant geometric
samplers for the normalized angle convention of Chapter 2. Do not claim
agreement with the exponential-based samplers before proving it.

## Periodic geometric derivatives on represented reals

Read `GeometricSinCos`, `GeometricQuarterEstimates`, `GeometricPeriodic`,
`GeometricQuarterDerivative`, and `GeometricDerivative` in that order. The
public rational names `GeometricTrig.sin` and `cos` use normalized angles;
the represented extensions are `sinAt` and `cosAt`.

`quarter_firstOrder` proves the actual geometric finite remainder. The
periodic proof transfers it to every rational interval of length at most
$\frac14$, splitting internally at a quadrant join when necessary.
`sin_derivative` and `cos_derivative` identify the full covered derivative at
an arbitrary valid represented real. `sinAt_congr` and `cosAt_congr` certify
input-name independence; their period theorems also allow arbitrary valid
represented inputs. No curvature partition is requested by the public laws.

`GeometricTaylorData.jet_derivative`, `jet_zero`, and `jetAt_small` package
the successive derivatives, geometric initial coefficients, and a uniform
rational bound. These results also preserve equivalent input names.

The proof uses rational circle algebra and real interval bounds. A finite
quadratic first-order error suffices for differentiability, but is not the
factorial remainder needed to identify the Taylor series. Keep that later
obligation explicit.

## Euler's ODE method: growth and rotation

Here Euler construction means Euler's numerical method for an initial-value
problem. It is independent of the later Taylor-series construction.

For real growth, the finite steps and their reciprocal upper bounds are

$$
L_N(q)=\left(1+\frac qN\right)^N,\qquad
U_N(q)=\frac{1}{L_N(-q)},\qquad N>|q|.
$$

`EulerFinite` proves refinement order and the shrinking gap directly by
finite rational algebra. `EulerReal` applies these bounds to the endpoints of
an arbitrary valid represented input, with a proved mesh schedule. The output
is valid and independent of the input name. `EulerReal.derivative`, in
`EulerRealDerivative`, uses finite difference-of-powers bounds to place every
secant between its endpoint values; shrinking then proves

$$
E(0)=1,\qquad E'(x)=E(x)
$$

for every valid represented real input. `EulerReal.value` descends to
`Numbers.Real` through a computable quotient lift. No power series defines
this function or proves its derivative.

For the imaginary version use our primary normalized angle. Write
\(C(x)=\cos(\pi x)\) and \(S(x)=\sin(\pi x)\) for the existing geometric
functions. Starting at \((1,0)\), finite Euler steps are

$$
(C_{k+1},S_{k+1})=(C_k-\pi hS_k,\;S_k+\pi hC_k).
$$

`EulerImaginaryFinite.state_error` compares these actual finite steps with
the geometric function using its proved quadratic local remainder. Iterating
the error inequality and bounding the finite amplification factor proves a
vanishing mesh error for both signs of the step. This is a direct numerical
ODE comparison, without a trigonometric or exponential series or an assumed
solution-uniqueness field.

`EulerImaginary` separately searches for sufficient precision in the represented
coefficient \(\pi\). Rational midpoint centers and their certified errors give
nested complex boxes. Its runtime evaluates only Euler steps, geometric
quadrature for \(\pi\), and interval arithmetic. The geometric sine and cosine
appear in the proof of error bounds, not in the Euler evaluator.
`numericalPi` uses a separate proved-equivalent sampling schedule so coefficient
accuracy is chosen independently of the Euler mesh.

`EulerImaginaryExtension` extends the rational sampler to every valid
represented real. Its exact `euler_identity` and `solves_rotation` establish

$$
Z(x)=C(x)+iS(x),\qquad Z'(x)=i\pi Z(x).
$$

The derivative statement is packaged as the two covered real component laws.
The input may be irrational, negative, or at a quadrant join; equivalent names
give equivalent outputs. `EulerImaginary.value` is an ordinary definition on
`Numbers.Real` with values in `Numbers.Complex`.

`EulerImaginaryCoordinates` provides `radianEval` by the proved reciprocal of
\(\pi\), and proves its circle identity and exact coordinate conversion:

$$
Z_{\mathrm{rad}}(\pi x)=Z(x).
$$

The separately checked derivative theorem is in the normalized coordinate;
a derivative theorem for `radianSample` would additionally use the coordinate
chain rule. This construction does not yet define a complex exponential away
from the imaginary axis or prove the general complex exponential laws.

Reproduce with `lake env lean --run scripts/check_euler_exponential.lean`
and `lake env lean --run scripts/check_euler_imaginary.lean`. The proof audits
reject exponential-series dependencies and unexpected axioms. Execution
checks cover nested enclosures, both signs, initial values, reciprocal
symmetry, finite precision search, and geometric anchor envelopes. They are
supplementary to the exact all-input kernel proofs. Multiple proved-equivalent
computations remain available: geometry explains the circle, Euler steps
explain the differential equation, and later series may offer faster evaluation.

### Agreement with factorial series and the full Euler power limit

The constructions now have exact comparison theorems. For every valid
represented real input, including negative and irrational inputs,

$$
E(x)=\sum_{k=0}^{\infty}\frac{x^k}{k!}
    =\lim_{N\to\infty}\left(1+\frac{x}{N}\right)^N.
$$

`EulerSeriesFinite.euler_factorial_error` proves the finite comparison first.
If \(\lvert x\rvert\le C\), the factorial prefix through degree \(N\) and
the Euler power differ by at most

$$
\frac{C^2 B(C)}{N},
$$

where \(B(C)\) is a rational finite-prefix-plus-tail bound. The proof compares
the falling-factorial binomial coefficients with the factorial coefficients;
it handles signed inputs. `EulerPowerLimit.approximation_error` controls the
other side of the comparison, at every sufficiently large integer step count.
It accounts for represented input uncertainty internally. The result is
`EulerSeriesIdentity.exponential_hasSum`, with the actual factorial terms,
and the exact `seriesAt_equiv_euler`. This comparison uses finite algebra and
shrinking bounds; it does not assume a general ODE uniqueness provider.

The existing primary rational algorithm `expPowerSeries` is included.
`EulerLegacySeries.adaptive_valid` checks its original adaptive interval
algorithm directly, and `adaptive_equiv_euler` identifies its value.
`seriesAt_rational` proves that the represented-input factorial evaluator
extends that primary sampler. This retains both algorithms, rather than
replacing a series computation with a call to the Euler evaluator.

On the normalized imaginary axis the analogous identities hold:

$$
Z(x)=\sum_{k=0}^{\infty}\frac{(i\pi x)^k}{k!}
    =\lim_{N\to\infty}\left(1+\frac{i\pi x}{N}\right)^N
    =\cos(\pi x)+i\sin(\pi x).
$$

`EulerImaginarySeries` gives convergence of both factorial coordinate series
and identifies their computed sum with the Euler rotation computation.
`imaginary_power_coordinates` checks that their four-phase coefficients are
precisely the powers of \(i\); `factorial_series_converges` states convergence
with the literal \(i^k/k!\) coefficients. `EulerImaginaryPowerLimit` proves convergence
of the full integer-step rotation powers at arbitrary represented inputs,
using the geometric remainder and an explicit finite error bound. These
comparisons preserve the original series-free real derivative and geometric
rotation proofs.

`EulerExponentialAgreement.real_three_way` and `imaginary_three_way` package
the results. `powerLimitAt` supplies a valid represented value using successive
integer-step powers, certified errors, and prefix intersections.
`powerLimitAt_equiv_series` identifies that actual computation with the
factorial evaluator; `real_values_three_way` equates all three quotient functions. `seriesValue_eq_eulerValue` and
`imaginarySeriesValue_eq_eulerValue` state literal equality on the quotient
number types. Both series evaluators and both finite power algorithms preserve
equivalent input names. The new general represented factorial evaluator uses
a conservative error bound; this does not claim that every evaluator has the
same performance.

The old display candidate `expEuler` remains distinguished from these certified
constructions. Its fixed radius is invalid in general: at input \(2\) its
first two displayed intervals are disjoint. The kernel-checked
`legacy_euler_candidate_not_valid` records that obstruction. The corrected
mathematical assertion is the full power-limit theorem with proved error
control; the invalid display boxes are not advertised as another real name.

Reproduce the exact comparisons and execution checks with
`lake env lean --run scripts/check_euler_agreement.lean`. The audit permits
only Lean's standard logical axioms, and the executable-dependency check keeps
the independent series and power programs separate from their comparison
targets.

## Applications downstream of Euler's formula

### Practical evaluation can choose a different route

The constructions used to explain or identify a function need not be executed
literally in practical computation. Geometry, Euler steps, factorial series,
and rational powers can each illuminate a different theorem. A numerical
evaluator may combine other proved-equivalent computations, selecting its
method from the input region and the requested precision.

For the exponential, possible strategies include reducing the argument to a
small interval, evaluating a local approximation with a certified remainder,
and reconstructing the answer through the multiplication and inverse laws.
For sine and cosine, periodicity and symmetry can first reduce the normalized
angle; a local polynomial or rational approximation can then supply certified
bounds. These are implementation strategies, not claims that optimized
dispatchers have already been built.

Such an evaluator must account for every error, including errors in constants
and argument reduction. Prove validity, representation invariance, and exact
agreement with the established function. Dispatch by certified finite
observations; overlapping cases must agree, and the intended input domain
must remain covered even when an exact comparison is undecidable. The
combined dispatcher is still a single computation on its declared domain.
No computation gains a privileged mathematical status by being faster or
more useful pedagogically.

### Checked applications

The optional [downstream application lesson](euler-applications.md) preserves
an applications-first reading order: factorial series, Euler's formula,
the convergent Cauchy product, addition identities, integer powers and
de Moivre's formula, then definite integrals.
Its Lean modules live in `subprojects/special-topics` and its audit requires
an actual proof dependency on `EulerImaginary.euler_identity`.

`EulerTrigIntegralApplications` constructs independent rectangle quadrature
and a closed-form theorem for arbitrary represented coefficients and ordered
rational endpoints. It proves the integral role, both semantic comparisons,
and coefficient-name invariance. `EulerSeriesMultiplication` connects the
general factorial-series multiplication law to the actual geometric circle
by comparing finite prefixes and the FTC-derived remainder.
`EulerTrigAddition`, `EulerTrigProducts`, and `EulerDeMoivre` prove addition,
subtraction, double-angle and product-to-sum identities, and the integer-power
formula for arbitrary represented real angles. These applications remain
downstream. Further rational trigonometric integral families still require
their whole-segment domain and substitution evidence.

## A represented constant integral

**Object and domain.** Supply any valid represented real constant on an ordered
rational endpoint interval. Its value may be irrational. The exact identity is

$$
\int_a^b c\,dt\simeq(b-a)c.
$$

**Construction pattern.** Finite constant rectangle bounds carry the uncertainty
of the supplied coefficient. Show their gap shrinks and certify the actual
scaled computation. No ambient class of integrands is required.

**Existing evidence.** `Integral.constant_hasIntegral` in
`IntegralSpecification` constructs the witness for the current rectangle
relation. Inspect its full type and its ordered-endpoint hypothesis.

**What it illustrates.** Subdivision and value-evaluation accuracy are different
issues: a constant has no spatial variation but can still require arbitrarily
accurate evaluation. A varying represented-valued monotone sampler requires
the combined two-index budget in Chapter 3, not an unproved equal-stage rule.

## Convex and concave FTC reference cases

`ComputableAnalysis.ConvexFTC` is reusable core support. Its downstream
`ConvexFTCExamples` module constructs square derivatives from rational outer
secants, proves the covered derivative identity for every valid represented
input, and certifies independent quadrature on every ordered rational endpoint
interval. Negating the actual secant construction supplies the concave case.
Both examples include signed derivative values. A further affine example uses
an arbitrary valid represented coefficient, without a rationality restriction.

Read `squareOuter`, `square_derivative`, `square_ftc`, `concave_ftc`, and
`affine_integral` in the companion. Reproduce with
`lake build ComputableAnalysis.ConvexFTCExamples` from
`subprojects/special-topics`. These proofs construct their evidence; the
integral identity is a conclusion. At a corner, supply a different justified
integration route rather than asserting an ordinary derivative there.

## Geometric Taylor expansions by repeated FTC

Read `GeometricFTCData`, `RepeatedFTC`, `GeometricTaylorFTC`,
`GeometricTaylorReal`, and `GeometricTaylorSeries` in order. Start with the
actual geometric derivative family. `RepeatedFTC.remainder_hasIntegral`
certifies each successive definite integral; `remainder_bound` integrates the
monomial majorants to obtain the factorial. `initial_coefficients` then
identifies the resulting geometric initial-value cycle.

The all-real bridge accounts for finite polynomial evaluation at represented
inputs. Only after the factorial error is proved to vanish do
`sin_taylor_converges` and `cos_taylor_converges` state the infinite expansions.
`sin_taylor` and `cos_taylor` identify the actual represented sum algorithms;
the corresponding validity and congruence laws accompany them.

Reproduce with `lake build ComputableAnalysis.GeometricTaylorSeries` and
`lake env lean scripts/check_geometric_taylor.lean`. The audit rejects complex
mathematics and independent trigonometric-series shortcuts, and requires the
actual geometric FTC dependencies. Lean shares a polymorphic natural-number
case matcher with an older namespace; the audited helper has only natural
number and unit arguments and constructs no complex value.

## Choosing another function

For changing curvature, consult `PiecewiseFTC.Pieces.ofOuter`, `hasIntegral`,
`ftc`, and `integral_equiv`. The companion `PiecewiseFTCExamples` checks a
cubic with concave and convex pieces and compares split/unsplit square
quadratures. For an infinite series, consult `ErrorSeries.Series` and
`HasSum.unique`; `ErrorSeriesExamples` identifies a geometric series with an
independently specified value. Its sine/cosine examples certify the radian
series sums, without claiming a new geometric comparison.

State the exact derivative, inverse, or integral identity and the full domain.
Choose a finite construction from the supplied function's actual structure.
Prove the needed validity, containment, shrinking, identification, and
comparison lemmas; reuse general conditional laws where their hypotheses fit.
If the bridge is absent, add the proof or record the target as open. Do not
create an interface that assumes the requested result.

For inverse targets use `skills/intermediate-value-construction/SKILL.md`;
for comparison use `skills/function-computation-identity/SKILL.md`; for a
particular rational or trigonometric integral use
`skills/elementary-definite-integrals/SKILL.md`. For a Taylor development from
the constructed function's actual derivatives, use the
[Taylor from FTC skill](../skills/taylor-from-ftc/SKILL.md), included in full
in the mission export. These repository paths are
resolved from the project root. General formalization guidance remains in
`skills/computable-analysis-formalization/SKILL.md`.
