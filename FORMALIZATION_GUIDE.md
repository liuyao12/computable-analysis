# Formalization Guide for Humans and LLMs

This is the short entry point for using this repository as a constructive,
rational-certificate foundation.  It is for a reader who wants to formalize a
new theorem from science, engineering, or first-year calculus without first
reading the entire Pi project.

The central rule is simple: state a computation as an algorithm returning
rational intervals or complex boxes, prove that its stages are valid and
refine, and connect it to the desired theorem through explicit finite
certificates. The comparison with other foundations is secondary; this guide
focuses on the interfaces available here.

For an external human or agent that needs a repeatable procedure rather than
just an API map, start with the public
[computable-analysis formalization skill](skills/computable-analysis-formalization/SKILL.md).
Its integral reference documents the per-function constructions, including a
shrinking rational bracket around a non-rational turning point.

For the focused calculus route, import
`ComputableAnalysis.CalculusFoundation`. It collects the circle, integral and
effective-FTC, power-series, exponential/logarithm, Fourier, and ODE layers
without importing the full benchmark catalogue. For a smaller dependency,
use the chapter entry points in this order:

```text
FunctionFoundation -> CircleFoundation -> IntegralFoundation
                   -> EffectiveCalculusFoundation
                   -> SeriesFoundation -> ExponentialLogarithmFoundation
                   -> DifferentialEquationsFoundation
```

These are routing modules, not claims that every imported interface is a
completed general theorem. Start with the smallest one that contains the
certificate you need.

## Read this first

The current strong point is checking specified rational and complex interval
arguments, finite linear systems, and certified special-function
representations. The following general constructions remain active targets:

- quotient rules for arbitrary interval evaluators (the affine-product finite
  certificate is checked; signed raw-real multiplication is now closed, while
  function-level products still require explicit local range bounds);
- general chain rules for arbitrary interval evaluators (the exact rational
  layer now has a budget-explicit `EffectiveDerivativeExact.compOfBudget`; an
  interval-valued composition still needs its own box-level contract);
- construction of an integral from every interval-regular function;
- general FTC, substitution, and automatic construction of bounded
  piecewise integration-by-parts certificates;
- a general multi-turn integral operator (the one-turn shrinking-bracket
  assembly is checked, but its endpoint identification remains
  function-specific);
- analytic certificates for the selected `exp`, `log`, `sin`, and `cos` raw
  functions, including `exp' = exp`;
- continuous matrix Peano--Baker and constructive linear
  Picard--Lindelöf; and
- numerical-error, PDE, units, and broad complex-domain infrastructure.

The integral boundary is intentional. `IntervalRegularOn` supplies finite
interval images, point containment, and a shrinking local modulus; it does not
by itself supply the cross-stage nesting required by `RealRaw.ValidCompute`.
An integral formalization must therefore add an explicit schedule certificate
(for example, `MonotoneDarbouxSchedule`) or a function-specific finite
assembly. This is the computable replacement for silently invoking compactness
or completeness of the classical real line.

A declaration may be a useful interface, a target `Prop`, or a fully proved
theorem.  The guide calls out that distinction.  A named `def` or `structure`
is never evidence that its intended mathematical theorem has been proved.

## Foundation audit

The project source has a small foundation boundary: rational arithmetic and
the interval constructions in `ComputableAnalysis.Basic`, followed by the
project's own modules. The manifest's external package is `checkdecls`, which
validates the blueprint's declaration links.

Before depending on a new module or publishing a material update, rerun this
compact audit from the repository root:

```bash
rg -n '^import\s+(Mathlib|Mathlib\.|Std\.|Batteries\.)' ComputableAnalysis
rg -n '\b(sorry|admit)\b' ComputableAnalysis
lake build computableanalysis
lake env .lake/packages/checkdecls/.lake/build/bin/checkdecls blueprint/lean_decls
```

The first two commands should print nothing.  The build and declaration check
then establish that the project modules and every Lean name cited in the
blueprint compile in the selected Lean toolchain.  This audit is intentionally
simple enough for an LLM or a contributor to repeat before treating the
repository as a dependency.

### Conformance status

The concrete theorem cores use rational algorithms that produce interval
boxes, with proofs of validity, nesting, overlap, and explicit shrinking
behavior.

This does not mean that every declaration is executable.  A few declarations
are deliberately retained as provisional interface packaging and are marked
`noncomputable`; in particular, the monotone-function wrappers in
`Calculus.lean`, `IntegralIdentities.lean`, and
`MonotonicityConvexity.lean`, the finite-partition refinement constructors in
`Calculus.lean`, the general integral-identity packages in
`IntegralIdentities.lean`, and algebraic-number operations in
`AlgebraicNumbers.lean`.  These are not evidence that the corresponding
general construction has been formalized.  They must either be replaced by
explicit algorithms or remain clearly labelled as interfaces/targets before
being used as computational results.

The practical rule is therefore: a theorem counts as standard-compliant only
when its public result is backed by an executable rational/finite constructor
and a checked certificate.  A `structure`, a `Prop`, or a `noncomputable def`
may organize the API, but does not by itself count as a completed
formalization.

## Fast navigation

Start with the smallest target module rather than importing
`ComputableAnalysis` (the root module imports the whole experiment).

| Need | Import | Start with |
| --- | --- | --- |
| Rational interval arithmetic and raw reals | `ComputableAnalysis.Basic` | `QInterval`, `RealRaw`, `RealRaw.Valid`, `RealRaw.Equiv` |
| Rational-domain complex functions and representations | `ComputableAnalysis.FunctionFoundation` | `FunctionRaw`, `PartialRealFunRaw`, `ComplexFunction`, domains, and representation transport |
| Rational circle and trigonometry | `ComputableAnalysis.CircleFoundation` | Rational geometry, arctangent/circle area, finite rotations, and stable complex coordinates |
| Integrals and effective FTC data | `ComputableAnalysis.IntegralFoundation` | Rectangle, piecewise, polynomial, arctangent, Stieltjes, and effective-FTC certificates |
| Effective-calculus proof contracts | `ComputableAnalysis.EffectiveCalculusFoundation` | Secant, derivative-bound, curvature, stabilization, inverse-search, and L'Hôpital interfaces |
| Power series and finite Fourier data | `ComputableAnalysis.SeriesFoundation` | Rational tails, finite termwise FTC, Fourier transforms, Gaussian prefixes, and the finite (n)-ball recurrence |
| Finite Fourier energy certificates | `ComputableAnalysis.FiniteFourierEnergy` | Rational complex coefficient energy, append/nonnegativity lemmas, and an interval certificate for a bounded omitted-energy tail |
| Finite separable multiple integrals | `ComputableAnalysis.FiniteNBallVolume` | `finiteProductIntegralNestedSum_factorized`, weighted rectangular sums, and the finite n-ball recurrence |
| Exponential and logarithm | `ComputableAnalysis.ExponentialLogarithmFoundation` | Taylor prefixes, tail bounds, rotation coordinates, and gap-aware inverse search |
| Linear differential equations | `ComputableAnalysis.DifferentialEquationsFoundation` | Scalar uniqueness, finite Peano--Baker algebra, rotation bridges, and finite ODE providers |
| Certified complex multiplication | `ComputableAnalysis.ComplexMultiplication` | `ComplexRaw.mul_valid`, `ComplexRaw.mul_equiv`, and the finite `QBox` bounds |
| Certified imaginary-axis input | `ComputableAnalysis.ComplexAffine` | `ComplexRaw.mulI`, `ComplexRaw.imaginaryAxis`, and exact rational complex-scalar actions |
| Rational function with a certified domain | `ComputableAnalysis.FunctionDomains` | `RatFun`, `RatFun.polynomialOnInterval`, `RatFun.polynomialOnInterval_compute_eq`, `RatFun.eval?_eq_some_of_defined`, `RatFun.eval?_eq_none_of_undefined`, `RatFun.oneOverX_defined_of_ne_zero`, `RatFun.oneOverXOnPositiveInterval`, `RatFun.oneOverXOnNegativeInterval`, `RatFun.DenominatorApartOnInterval`, `RatFun.onRegularInterval` |
| Interval functions, continuity, and integral certificates | `ComputableAnalysis.Calculus` | `FunctionOnInterval`, `IntervalRegularOn`, `Integral.nondecreasingDarbouxDyadicStage`, `Integral.generalConstructionFor`, `Integral.ConstructionFor` |
| Focused calculus foundation | `ComputableAnalysis.CalculusFoundation` | The dependency-checked umbrella entry point for all scoped calculus layers, finite multiple-integral, and finite complex-path layers |
| Finite monotone decomposition with non-rational turns | `ComputableAnalysis.TurningPointIntegral` | `Integral.TurningPointBracket`, `Integral.TurningBracketIntegralCandidate`, `Integral.MultiTurnIntegralCompletion`, `Integral.SingleTurnIntegralCompletion.constructionFor` |
| Rational finite-difference derivatives | `ComputableAnalysis.Differential` | `HasDerivativeOnInterval`, `HasForwardDerivativeAt` |
| Sector-area time | `ComputableAnalysis.SectorAreaReparametrization` | `angleOnUnit`, `angleOnUnit_hasDerivative`, `angleOnUnitRegular_intervalRegular`, `angleOnUnitRegular_invertible`, `angleAt_equiv_two_arctanGeom` |
| Finite rational circle powers | `ComputableAnalysis.RationalCircle` | `RationalCircle.Trigonometry.pointPow`, `pointPow_add`, `pointPow_mul`, and `pointPow_normSq_of_unit` |
| Definite-integral-to-endpoint packages and concrete arctangent work | `ComputableAnalysis.IntegralIdentities` | `Integral.DefiniteIdentityFor`, `IntegralIdentities` |
| Finite arithmetic, geometric, and power sums | `ComputableAnalysis.Series` | `Series.arithmeticSum_eq`, `Series.geometricSum_eq`, `Series.powerSum`, and the low-degree closed forms |
| Finite Basel-series certificates | `ComputableAnalysis.DirichletSeries` | `zetaTwoPartial_nonneg`, `zetaTwoFiniteTail_le_telescoping`, `zetaTwoInterval_nested`, and `zetaTwoRaw_validCompute` |
| Formal power series and rational tail bounds | `ComputableAnalysis.PowerSeries` | `FormalPowerSeries`, `RationalMajorant` |
| Finite term-by-term FTC for Taylor prefixes | `ComputableAnalysis.FiniteTaylorFTCInterface` | `FinitePolynomial.finiteTaylorFTC_step`, `FinitePolynomial.finiteTaylorFTC_prefix` |
| Finite sine primitive and half-period bridge | `ComputableAnalysis.FiniteSineIntegral` | `FiniteSineIntegral.halfAnglePrefix_cosine_complement`, `halfPeriodSineRaw_contains_halfAnglePrefix`, and the checked stage-four/six/eight/ten rational prefixes |
| Finite exponential tail certificates | `ComputableAnalysis.FiniteExponentialTaylor` | `FiniteExponentialTaylor.scheduled_expTaylorPrefix_remainder_le`, `FiniteExponentialTaylor.scheduled_expTaylorPrefix_enclosure` |
| Current first-year derivative ledger | `ComputableAnalysis.FirstYearCalculus` | `checked_power_series_table`, `RealElementary` |
| Positive powers, exponential/log interfaces | `ComputableAnalysis.ElementaryFunctions` | `exp.PositiveRealRaw`, `exp.RationalPowerExtension`, `exp.ExponentialFunction` |
| Direct scalar ODE uniqueness | `ComputableAnalysis.ScalarODEUniqueness` | `ScalarODE.DirectMeshHalvingCertificate`, `SelfDerivativeDirectMeshComparison` |
| Discrete linear ODE / Peano--Baker core | `ComputableAnalysis.PeanoBaker` | `LinearODE.DiscreteLinearSystem`, chronological products, finite Duhamel sums, the forced-oscillator recurrence `HarmonicOscillator.trajectory_position_secondDifference`, exact square-zero transitions, and the reusable `PeanoBakerFactorialRemainderCertificate` |
| Finite ordered-simplex volumes | `ComputableAnalysis.PeanoBaker` | `orderedSimplexVolume`, `orderedSimplexVolume_eq_closed`, `constantPeanoBakerSimplexTerm_eq_orderedSimplexVolume` |
| Certified complex rotation series | `ComputableAnalysis.RotationSeries` | `rotationExpRaw`, `rotationCosRaw`, `rotationSinRaw`, and their validity/rate theorems |
| Bounded rotation continuity | `ComputableAnalysis.RotationCalculus` | `uniformRotationCosOnTwo`, `uniformRotationSinOnTwo`, and their epsilon--delta theorems |
| Common-prefix rotation IVP candidate | `ComputableAnalysis.RotationInitialValues` | `uniformRotationCosOnTwo_zero_equiv_one`, `uniformRotationSinOnTwo_zero_equiv_zero`, `uniformRotationNegSinOnTwo_equiv_neg_sin`, `uniformRotationOnTwo_rotationInitialCertificate` |
| Represented-angle rotation lift | `ComputableAnalysis.RotationLift` | `RotationLift.HalfPiInput`, `rotation`, and its finite Cauchy certificate |
| Algebraic branches and square roots | `ComputableAnalysis.AlgebraicFunctions` | source header and the unit-interval square-root examples |
| Complex interval polynomial checks | `ComputableAnalysis.ComplexInterval` | `QBox.evalPoly`, `IsApproxRootAt` |
| Finite complex path calculus | `ComputableAnalysis.ComplexPathIntegral`, `ComputableAnalysis.FiniteComplexPathCertificate` | `polygonalIntegralRawEntire_valid`, closed constant/polynomial differential exactness, and rational polygonal paths |
| Finite multiple integrals and n-balls | `ComputableAnalysis.FiniteNBallVolume`, `ComputableAnalysis.FiniteGaussianIntegral` | `finiteProductSum2D_factorized`, `finiteProductIntegralSum2D_weighted_stage`, Gaussian Taylor-prefix/tail ladders, and `nBallVolumeModel_recurrence`/`nBallVolumeModel_nonneg` |
| Finite FTA root certificates | `ComputableAnalysis.FTA` | `monicLinear_has_computable_root`, `rationalLinear_has_computable_root`, and the rational quadratic discriminant witnesses |

The Gaussian prefix now exposes the reusable finite termwise-integration
contract through `gaussianEvenIntegralPrefix_succ` and
`gaussianEvenIntegralPrefix_term_difference`.  The named term and finite tail
majorant add a direct remainder contract through
`gaussianEvenIntegralPrefix_remainder_abs_le`.  These identities concern only
finite Taylor sums; the remainder is now packaged as the interval
`gaussianEvenIntegralPrefix_interval`, with exact containment and width
theorems `gaussianEvenIntegralPrefix_interval_contains` and
`gaussianEvenIntegralPrefix_interval_width`.  An improper Gaussian integral
still requires a separate tail certificate.

For the mathematical status and intended dependency order, use
[GOALS.md](GOALS.md).  For a readable, declaration-linked account, use the
[blueprint](blueprint/README.md).  The derivative table is in
[`blueprint/src/04-infinite-series.tex`](blueprint/src/04-infinite-series.tex),
not in this guide.

### Benchmark admission rule

The Wiedijk benchmark is a source of targets. An entry is admitted to the project
scoreboard only if its Lean statement is native to this repository: its real
values must be `RealRaw`/abstract `Real` values, rational interval algorithms,
or finite algebraic certificates. Classical statements are represented here
through the project's abstract computable-real and complex-function
interfaces.

When the classical theorem genuinely needs completeness, arbitrary limits,
Lebesgue measure, or another noncomputable object, we record a scoped
constructive replacement with the hypotheses and conclusion visibly
restricted. The replacement counts only under that scoped name; it must not
be presented as a proof of the unrestricted classical statement. Routine
finite lemmas are reused from the available foundation.

### Benchmark routing

The benchmark alignment is maintained in
[`blueprint/src/08-roadmap.tex`](blueprint/src/08-roadmap.tex).  It currently
records 52 scoped project-relevant finite, rational-coordinate, or
certificate-level cores.  The machine-checked registry and its coverage
invariants are in
[`ComputableAnalysis/WiedijkScoreboard.lean`](ComputableAnalysis/WiedijkScoreboard.lean).
The easiest entries are distributed across
Foundations, Circle and Trigonometry, Infinite Series, Effective Calculus,
Algebra and FTA, and Linear Differential Equations; the remaining benchmark
numbers have explicit supporting or out-of-scope dispositions there.  Use the
roadmap number and chapter placement as the authoritative starting point
rather than treating the benchmark as a claim of full classical library
coverage.

### Module atlas

Use this as a routing index, not as a claim that every module exposes a
finished general theorem.

| Family | Modules | Use them for |
| --- | --- | --- |
| Foundation | `Basic`, `Algebraic`, `AlgebraicNumbers`, `AlgebraicFunctions`, `FunctionDomains`, `Extension`, `Calculus`, `Differential`, `MonotonicityConvexity`, `FTC`, `FiniteMonotoneSequenceInterface` | Raw interval representations, domains, continuity, inverse branches, finite derivatives, monotone bounded-process intervals, and integral/FTC certificate interfaces |
| Elementary functions and series | `Elementary`, `ElementaryFunctions`, `Exp`, `ExpProofs`, `Logarithm`, `PowerSeries`, `Series`, `Taylor`, `FirstYearCalculus` | Power-series algorithms, rational majorants, exp/log comparison interfaces, and the current formal derivative ledger |
| Integrals and special computations | `TurningPointIntegral`, `IntegralIdentities`, `ArctanGeometry`, `ArctanPresentations`, `AbelianIntegrals`, `ComplexPathIntegral`, `DirichletSeries`, `Basel`, `FTA` | Concrete interval constructions and theorems/targets connecting them to geometric or series algorithms |
| Geometry, Pi, and ODEs | `RationalCircle`, `TrigSpecialValues`, `GaussSeventeen`, `Pi`, `PiProofs`, `ComplexAffine`, `ComplexMultiplication`, `PiComplex`, `Nilakantha`, `PeanoBaker`, `RotationSeries`, `RotationLift`, `SectorAreaRotation` | Rational-circle geometry, explicitly status-marked special values, Pi coverage tests, certified raw complex multiplication and exact rational complex-scalar actions, the certified `i*pi/2` input bridge, finite ODE algebra, the certified imaginary-axis complex series, and the sector-clock endpoint's factorial-rotation transport |
| Polynomial and complex checks | `Polynomial`, `ComplexPolynomial`, `ComplexInterval` | Exact polynomial algebra and rational complex-box root checks |

`Playground`, `MembershipCheck`, and the repair/check files are development
support rather than a stable downstream API.  Prefer a theorem in one of the
families above, and consult its module header before using it.

## Representations to keep separate

Most mistakes come from conflating these layers.

| Object | Meaning | What it does not provide automatically |
| --- | --- | --- |
| `QInterval` | A rational enclosure `[lo, hi]` | A real number or a shrinking proof |
| `RealRaw` | A sequence of rational interval boxes | Validity; supply `RealRaw.Valid` |
| `RealRaw.Equiv` | Overlap-based equality of two valid raw reals | Equality of implementations by definitional reduction |
| `FunctionRaw` | One domain-indexed complex-box computation | Validity; supply `FunctionRaw.Valid` |
| `ComplexFunction` | An abstract complex special-function handle with certified concrete representations | A claim that it belongs to a preselected classical function space |
| `PartialRealFunRaw` | A real-axis or restricted function with a pointwise domain | A whole-interval domain certificate |
| `PartialRealFunction` | An abstract real-axis view when needed | A replacement for the complex function foundation |
| `FunctionOnInterval` | A partial function certified at every rational point of `[a,b]` | Continuity, interval regularity, differentiability, or integrability |

For representation management, `RealRaw.equiv_of_common_anchor` is the
standard shortcut: two valid algorithms that are each equivalent to the same
valid anchor are equivalent to one another.  The anchor is proof-side data;
the runtime continues to evaluate the chosen algorithm directly.

The function-level analogue is
`RealFunRaw.equivalentWith_of_common_anchor`.  It applies the same rule
pointwise on the overlap of two partial domains, requiring only that the anchor
be defined at those shared inputs.  This is the preferred way to connect
independently implemented special-function computations without duplicating
their evaluation procedures.

### Functions: complex first, concrete first, abstract only when useful

The library is representative, not encyclopedic.  Formalize one complete
example for each genuinely different computational pattern; routine variants
should be obtained by algebraic transport, restriction, or composition.  A
piecewise function such as `|x|` is handled by splitting its domain into the
corresponding pieces and reusing the existing integral certificate.  This
keeps the blueprint focused on reusable proof contracts rather than a catalog
of near-duplicate functions.

The same rule applies to notation and normalization: `sin (pi * x)` and a
rescaled presentation such as `sin (pi / 2 * t)` are one computational pattern
when a rational change of variable transports the domain and certificate.
Choose the representation that makes the current proof easiest, and record
the transport; do not create a second special-function theory for the change
of coordinates.

Use `FunctionRaw` for one concrete complex computation:

```text
complex domain + (z, stage) ↦ rational complex box
```

The domain is part of the representation.  It is not necessary to decide
whether the function is “continuous,” “analytic,” or any other classical
category before formalizing a useful theorem.  Use
`FunctionRaw.realPartOnRealAxis` or another certified restriction when an
argument needs real inputs.  Fourier constructions should likewise begin with
complex-valued functions and restrict to a real parameter line only when that
is the theorem’s actual domain.

When a complex special function has several useful algorithms, package them as
a `ComplexFunction`.  Each implementation carries:

- pointwise validity on its own domain; and
- an explicit `AgreeOnOverlap` proof with the preferred implementation.

The agreement statement is deliberately only about the intersection of the
domains.  If a new representation is compared through an intermediate one,
the intermediate domain must cover the relevant intersection; otherwise prove
the new common-domain agreement directly.  This prevents an invalid appeal to
transitivity across changing domains.

For complex numbers themselves, use `Complex.withAlternativeFrom` or
`Complex.withAlternativeFromImplementation` when the new algorithm is proved
equivalent to an existing non-preferred implementation.  The constructor
stores the composed edge to the preferred node, so the source proof remains a
single local equivalence edge while the registry remains a finite spanning
tree.
At the raw-box level, `ComplexRaw.equiv_of_common_anchor` provides the same
transport rule as `RealRaw.equiv_of_common_anchor` for complex algorithms.
At the function level, use
`FunctionRaw.agreeOnCommonDomain_of_common_anchor`: provide validity for both
outer computations and the anchor, plus explicit anchor-domain coverage on
their common inputs.  This is the complex-function version of the spanning
tree rule; it does not assert agreement outside the shared domain.

For `ComplexFunction`, use `ComplexFunction.withAlternativeFrom` or
`ComplexFunction.withAlternativeFromImplementation` when the new algorithm is
proved equivalent to an existing representation.  Supply the explicit domain
coverage hypothesis for the intermediate representation; the constructor then
composes the local equivalence edge with the existing path to the preferred
function.  This keeps partial domains honest while allowing a genuine
spanning-tree registry.

At a shared rational input, use
`ComplexFunction.Representation.eval_equiv_preferred` to retrieve the stored
pointwise equivalence directly, without manually unpacking the representation.

For partial real functions, the preferred representation can serve as the
spanning node for two alternative views.  When the source domain is known to
lie in the preferred domain, use
`PartialRealFunction.Representation.equiv_on_common_domain` to compare it with
any target representation at a shared rational input.  The theorem transports
through the preferred evaluator and keeps domain hypotheses explicit; it does
not pretend that two representations agree outside their common domain.

Recommended pattern:

```lean
def preferred : PartialRealFunRaw := ...
theorem preferred_valid : preferred.Valid := ...

def alternate : PartialRealFunRaw := ...
theorem alternate_valid : alternate.Valid := ...
theorem alternate_agrees :
    preferred.AgreeOnCommonDomain alternate := ...

def specialFunction : ComplexFunction :=
  (ComplexFunction.ofRaw preferred preferred_valid).withAlternative
    alternate alternate_valid alternate_agrees
```

This is the project’s “pre-classical” stance: formalize the special function
and the complex algorithms actually needed, rather than first postulating a
general function space and proving a classification theorem.

For a rational formula with no singularities, begin with
`FunctionOnInterval.exactRat`.  For a rational quotient, begin with `RatFun`
and prove `RatFun.DenominatorApartOnInterval`; pointwise rational
definedness alone does **not** exclude an irrational pole inside the interval.
For example, `1 / (x^2 - 2)` must not be treated as regular on `[1,2]`.

## Standard workflow for a new theorem

1. **Reduce the claim to a certified rational interval.**  Select rational
   endpoints and state all denominator, positivity, orientation, and branch
   hypotheses.  Split a problem into monotone pieces when that is the real
   mathematical reason a bound holds.
2. **Choose the representation.**  Use an exact rational evaluator for a
   polynomial identity, a `RatFun` plus a domain certificate for a quotient,
   or a `RealRaw` interval algorithm for an inexact elementary value.
3. **Prove validity before using the value.**  An interval algorithm needs the
   appropriate `RealRaw.Valid`/`RealRaw.ValidCompute` theorem.  Two algorithms
   are compared by `RealRaw.Equiv`, never by assuming a completed real field.
4. **Add the needed regularity certificate.**  Use `IntervalRegularOn` for
   subinterval enclosures and its theorem
   `IntervalRegularOn.epsilonDeltaContinuous` for literal rational
   epsilon--delta continuity.  A function being defined at all rational
   points is weaker than interval regularity.
5. **Add a calculus certificate.**  A derivative is a
   `HasDerivativeOnInterval` finite-difference enclosure.  Its evaluator
   precision may depend on the rational step; this is essential for inexact
   interval values.
6. **Close the theorem at the correct level.**  For a pointwise equality,
   prove an interval or raw-real equivalence.  For a definite integral, supply
   an integral construction and an endpoint theorem.  For an ODE, first state
   the finite recurrence or the continuous certificate actually available.
7. **Only then expose a friendly formula.**  The familiar formula is the
   public theorem; the raw implementations and bounds are its proof data.

### Constructive inverse branches

For a computable inverse, package a branch-local
`InvertibleFunctionOnInterval`: source interval, interval regularity, weak
monotonicity, and an `EffectiveInverseSeparation` schedule. A target is an
`InRangeRaw`, carrying both its raw validity and endpoint-range evidence.
Then provide `InverseBisectionSearch` data for each target and assemble it with
`inverseRawOfSearch`.

The complete identity provider in `ComputableAnalysis.IdentityInverse` is the
minimal template. Its preimage computation reuses the target box, but still
proves every source-subinterval and forward-overlap field. Nonlinear branches
must replace only that search computation; they must not replace the range or
separation obligations with a classical inverse-function theorem.

### Do not multiply routine cases

Formalize one representative for a reusable process, then reuse its generic
closure lemmas.  Do not create separate theorem families merely because a
routine example changes sign, uses a scalar multiple, or swaps equivalent
coordinates; add a new declaration only when the domain, computation, or
certificate is genuinely different.  In particular, a piecewise function is
handled by finitely many interval integrals and a finite assembly theorem.
The absolute-value example in `PrimitivePiecewiseFTC` is the reference
pattern: two affine cell computations, followed by one finite telescope.
For the list-level transport itself, use
`Integral.finiteRawListEquiv_map_of_forall`; it lifts corresponding cell
equivalences across a finite indexed list and keeps the assembly proof
independent of the particular function formula.

For curvature, the square is the reference instance.  Use
`ExactFunction.square_secantSlope_eq_add` to reduce its secant to a rational
sum, and `ExactFunction.square_convexOn` to obtain convexity on any rational
interval.  This is the preferred template for a new curvature-driven FTC
example: prove one finite secant identity for the evaluator, then feed it into
the existing curvature/derivative-bound contracts.  Do not duplicate the
theorem for every polynomial power unless its application needs a genuinely
different certificate.  The raw bridge is
`square_secantSlopeInterval_eq` followed by
`ExactFunction.squareRaw_curvatureOnSubinterval`; its exact singleton interval is already a
valid finite-stage curvature enclosure.  Pair it with
`ExactFunction.squareRaw_monotoneDerivativeBoundMethod` (the endpoint range of
`2*x`) and `ExactFunction.squareRaw_derivativeBoundFromCurvature` to obtain the
derivative-bound input expected by the FTC layer.  The complete square
certificate is `squareCurvatureFTCData`, with endpoint equivalence proved by
`squareCurvatureFTC_equiv_endpoint`.

For an effective FTC proof, do not force all computations to use one stage.
`TwoStageCandidateDerivativeFTC` allows the derivative evaluator and the
primitive endpoint evaluator to choose independent stages. The derivative
stage builds the cell bounds; the endpoint stage supplies the common-stage
finite telescope. The public closure theorem is
`ComputableAnalysis.twoStageCandidateDerivativeFTC`, while
`TwoStageCandidateDerivativeFTC.boundedIntegralRaw_equiv_endpointDifference`
transports the resulting raw integral to the canonical endpoint difference.
This separation is useful for nested-radical or other staged special-function
evaluators whose pointwise and endpoint computations have different natural
schedules.

For finite Fourier work, make cancellation a certificate with explicit
rational-complex fields rather than an implicit root-of-unity assumption.
`FiniteFourierBlockCancellationCertificate` is the reusable interface; the
ready-made `quarterTurnConstantBlockCancellationCertificate` is the reference
instance, and its repeated-block theorem can be used directly in later finite
stage constructions.

When a Fourier computation has finite support, use
`finiteSupportFourierSeries_stabilized_equiv`. It proves that the stabilized
complex raw object is equivalent to the exact rational-complex finite
transform, so a finite sample table does not need a second convergence proof.
Reserve `EffectiveFourierSeries` tail certificates for genuinely unbounded
coefficient families.
Such a certificate exposes `EffectiveFourierTailCertificate.stageBox` and
`future_stage_in_stageBox`, a single rational-complex enclosure for every
future stage.  Its exact coordinate budgets are exposed by
`stageBox_width` and `stageBox_height`, both equal to `2 * radius k`.

Use `rg` to discover nearby examples before inventing a new interface:

```bash
rg -n 'HasDerivativeOnInterval|ConstructionFor|IntervalRegularOn' ComputableAnalysis
rg -n 'DefiniteIdentityFor|epsilonDeltaContinuous' ComputableAnalysis
rg -n 'theorem .*valid|theorem .*equiv' ComputableAnalysis/<target>.lean
```

Then place a small `#check` block in a scratch Lean file and build only the
module you are using:

```lean
import ComputableAnalysis.IntegralIdentities

open ComputableAnalysis

#check FunctionOnInterval.exactRat
#check IntervalRegularOn.epsilonDeltaContinuous
#check HasDerivativeOnInterval
#check Integral.ConstructionFor
#check Integral.DefiniteIdentityFor
#check IntegralIdentities.coordinateOnUnitDerivative
```

```bash
lake build ComputableAnalysis.IntegralIdentities
```

## Derivatives: what is usable now

The exact affine and square examples in `Differential.lean` are complete
worked models:

- `FunctionOnInterval.exactRatAffineDerivative`;
- `FunctionOnInterval.exactRatIdDerivative`; and
- `FunctionOnInterval.exactRatSquareDerivative`.

There are also genuine full interval derivative certificates on `[0,1]` for:

- `IntegralIdentities.coordinateOnUnitDerivative` (`d/dx x = 1`);
- `IntegralIdentities.arctanIntegralRectangleOnUnit_hasDerivative`
  (`dA_rect/dx = 1/(1+x^2)`); and
- `IntegralIdentities.coordinateTimesArctanIntegralRectangleOnUnit_hasDerivative`
  (`d(x A_rect)/dx = A_rect + x/(1+x^2)`).

`FunctionOnInterval.scaleRat` and
`HasDerivativeOnInterval.scaleRat_of_nonneg` now give the reusable scalar
rule for every nonnegative rational factor.  The caller supplies an internal
stage and proves `r * precision(internal) <= precision(output)`; the special
case `HasDerivativeOnInterval.scaleRat_two` packages the standard
`2*(n+1)` schedule.  The sector-area module applies that rule to the rectangle
arctangent.  Its `angleOnUnit` has derivative
`speedOnUnit`, whose exact rational value is
`RationalCircle.Stage.sectorAreaSpeed t = 2/(1+t^2)`;
`angleAt_equiv_two_arctanGeom` supplies the pointwise bridge to the geometric
angle representation.  The same module now proves the quantitative finite
gap `x + 1/(n+1) <= y -> Theta_x.hi < Theta_y.lo` at stage `64*(n+1)`,
and packages it as `angleOnUnit_effectiveInverseSeparation`.

The unrestricted rational scalar rule is now also available as
`HasDerivativeOnInterval.scaleRat`.  Its budget uses `qabs r`, and the proof
splits the sign explicitly: nonnegative scaling uses interval multiplication,
while a negative scalar is reduced to nonnegative scaling followed by
endpoint negation.  This makes linear combinations sign-complete without
silently assuming an ordered completed field.

`HasDerivativeOnInterval.linearCombinationOfCommonSchedule` packages the
next composition step: after the two signed-scalar certificates have been
constructed, it adds them on a common chart and pays the doubled internal
precision budget.  Its explicit schedule equalities are the intended input
for linear ODE residuals and finite Taylor coefficient combinations.

The exact rational chain rule is available as
`ExactFunction.differenceQuotient_comp_factorization`,
`ExactFunction.differenceQuotient_comp_error_le`, and
`ExactFunction.EffectiveDerivativeExact.compOfBudget`.  The constructor keeps
the inner increment, outer step-radius transport, and weighted error budget
explicit.  It is a reusable proof interface for composed computations, not an
automatic theorem about arbitrary functions or limits.

Negation is also closed at the interval level:
`FunctionOnInterval.neg` reverses endpoint boxes without changing their
width, and `HasDerivativeOnInterval.neg` proves the corresponding
`D(-f) = -Df` rule at the same evaluator stages.
`FunctionOnInterval.sub` is defined as addition with negation, and
`HasDerivativeOnInterval.subOfCommonSchedule` supplies the corresponding
finite subtraction rule.  These operations are now available for residuals,
endpoint differences, and linear combinations in later chapters.
`angleOnUnitRegular` is the cofinally accelerated presentation whose
stage `n` uses that rectangle stage; its
`angleOnUnitRegular_intervalRegular` endpoint-image evaluator and
`angleOnUnitRegular_invertible` package now supply the interval
regularity, monotonicity, and strict separation required by the constructive
inverse interface.  The data-valued inverse search, followed by curve
reparametrization and vector uniqueness, remain separate tasks.
At the unit endpoint,
`regularAngleAt_one_equiv_quarterTurnRaw_one` directly identifies the
accelerated clock with the normalized geometric quarter-turn raw.
At the unit endpoint,
`PiProofs.pi.sectorAreaAngleOne_equiv_halfPi` now closes the finite transport
`Theta(1) ≡ pi/2`; this is an endpoint equivalence, not yet a general inverse
or reparameterized-curve construction.
`SectorAreaRotation.halfPi` independently exposes that accelerated endpoint
as a `RotationLift.HalfPiInput`: every rectangle box is checked in `[1,2]`
from the rational endpoint-kernel bounds, while the accelerated width bound
supplies the remaining input data.  `SectorAreaRotation.rotation_equiv_geometricRotation` then
transports the resulting stabilized factorial rotation to
`GeometricPiRotation.rotation`.  This closes the sector-clock input transport
only; the separate geometric endpoint identity remains the vector-uniqueness
step.

`FirstYearCalculus.checked_power_series_table` proves the coefficient-shift
identities for exp, sin, cos, sinh, and cosh. The primary series API calls
this operation `FormalPowerSeries.coefficientShift` and its relation
`HasCoefficientShift`; the older `derivative` names remain compatibility
aliases. At a chosen expansion point this is linear Taylor-coefficient data,
not yet an interval-analytic derivative theorem for the corresponding boxed
raw functions. Downstream proofs must preserve that distinction.

The finite polynomial bridge is now checked at the rational level:
`FinitePolynomial.qabs_normalized_power_differenceQuotient_sub_monomial_le`
proves an explicit `|h|` error bound for the literal quotient of
`x^(n+1)/(n+1)` against `x^n` on any supplied rational bounded box.
`FinitePolynomial.normalizedMonomial_hasDerivativeOnInterval` packages that
bound as a full two-sided interval derivative certificate with an explicit
dyadic half-decay step schedule.  It is also the right finite algebra for the
termwise factorial-series bounds needed by exponential.
`FinitePolynomial.monomialSecantDerivativeBound` and
`FinitePolynomial.monomial_hasDerivativeOnInterval` now scale that certificate
by (n+1), giving the general finite power rule
`d(x^(n+1))/dx = (n+1)x^n` on every supplied bounded rational chart.
The cubic specialization is now exposed as
`FinitePolynomial.cubeSecantDerivativeBound` and
`FinitePolynomial.cube_hasDerivativeOnInterval`: rationally scaling the
normalized `x^3/3` certificate yields the exact finite derivative
`d(x^3)/dx = 3x^2` on any supplied bounded rational interval.  This is a
complete polynomial FTC input, not an appeal to a classical derivative limit.
`FinitePolynomial.taylorPrefix_hasDerivativeOnInterval` materializes any
formal coefficient stream as a finite rational Taylor polynomial and derives
its interval derivative from `FormalPowerSeries.coefficientShift`. This is
the intended hand-off from Chapter 4's algebra to Chapter 6's derivative
certificates; no infinite-series tail is differentiated at this point.
For interval regularity itself, `Integral.exactPow_lipschitz_on_minusOne_one`
and `Integral.exactRat_pow_intervalRegularOn_minusOne_one` expose the
parametric monomial certificate on `[-1,1]`: the rational power-difference
recurrence gives the natural Lipschitz bound `n`, including `n = 0`.
The matching primitive algebra is exposed by
`Integral.monomialPrimitiveRaw`,
`Integral.monomialPrimitiveEndpointDifference`, and
`Integral.monomialPrimitiveEndpointDifference_adjacent_additive`; these
objects telescope over rational partitions before any limiting integral
argument is introduced.
For the finite quadrature itself,
`Integral.uniformLeftEndpointSum_pow_eq_scaled_powerSum` identifies the
left-rectangle sum for `x^n` with a scaled `Series.powerSum`. This keeps the
value-identification problem in finite rational arithmetic; convergence or
endpoint overlap is a separate theorem obligation.
The right-endpoint counterpart is
`Integral.uniformRightEndpointSum_pow_eq_scaled_powerSumBlock`, and for a
positive exponent
`Integral.uniformRightEndpointSum_pow_sub_left_eq_scaled_last_power` gives
the exact left/right rectangle gap. This is the finite shrinking certificate
used before identifying the common endpoint value.
With positive mesh count it normalizes further to exactly `1 / n` via
`Integral.uniformRightEndpointSum_pow_sub_left_eq_inv_of_pos`, making the
precision schedule immediate.
The resulting constructive integral object is available for every monomial
through `Integral.exactRat_pow_integral_certificate`, with validity proved by
`Integral.exactRat_pow_integral_raw_valid`. This is intentionally separate
from a theorem identifying the object with the closed form `1 / (n + 1)`.
The exponent-zero regression
`Integral.exactRat_zero_integral_raw_equiv_one` confirms that the generic
certificate specializes to the exact constant integral without unfolding the
private Darboux folds.

The exponent-one regression
`Integral.exactRat_one_integral_raw_equiv_half` checks the first nonconstant
case through the public affine left/right sum formulas.

The quadratic regression is already complete as well:
`Integral.exactRat_square_integral_raw_equiv_one_third` proves the generic
finite dyadic box contains `1 / 3`, using the finite sum-of-squares identity.
The cubic, quartic, and fifth-degree values are exposed by
`Integral.exactRat_cube_integral_raw_equiv_one_fourth`,
`Integral.quarticIntegralEffectiveFTC_equiv_one_fifth`, and
`Integral.fifthIntegralEffectiveFTC_equiv_one_sixth` respectively.
The same rational power induction supplies
`Integral.exactRat_pow_nondecreasing_on_unit` and a compatible
`Integral.exactRat_pow_monotoneConstructionFor`, so the monomial can be fed
through either the Lipschitz dyadic or monotone Darboux interface.
`Integral.exactRat_pow_monotoneIntegralFor_valid` proves the monotone wrapper
valid, while `Integral.exactRat_pow_monotoneIntegralFor_eq_dyadicRaw` records
that both wrappers are literally the same underlying interval computation.
For a prefix containing a linear term,
`FinitePolynomial.taylorPrefixShift_at_zero` identifies that certified
derivative polynomial at zero with the original coefficient `c 1`.
For an expansion centered at a rational `a`, use
`FinitePolynomial.taylorPrefixAt` and
`FinitePolynomial.taylorPrefixAt_hasDerivativeOnInterval`: the local box
assumptions are `-C <= lower - a` and `upper - a <= C`, and
`FinitePolynomial.taylorPrefixShiftAt_at_basepoint` proves that the certified
derivative at `a` is again `c 1`.  Thus the coefficient interpretation is
translation-invariant without invoking an ambient real line.
For the finite integral identity itself, import
`ComputableAnalysis.FiniteTaylorFTCInterface`: use
`FinitePolynomial.finiteTaylorFTC_step` for one added monomial and
`FinitePolynomial.finiteTaylorFTC_prefix` for the complete finite prefix.
These are rational endpoint identities; the tail certificate and the raw
real representation remain separate obligations.
At the quantitative level, `FinitePolynomial.SecantDerivativeBound.add`,
`scaleRat`, and `mul` compose finite derivative certificates.  The product
constructor asks for rational bounds for each factor and its proposed
derivative on the local box; its explicit coefficient includes the finite
secant corner term.  Supply those majorants rather than invoking an
unqualified product-rule limit.  `FinitePolynomial.SecantDerivativeBound.mulToHasDerivativeOnInterval`
now hands that product certificate directly to the interval derivative
interface, producing the exact rational product chart and the derivative
chart \(f g' + g f'\).  This is the project’s bounded, finite version of the
product rule; no completeness or unbounded limiting theorem is hidden in the
wrapper.
The local FTC hand-off is explicit as well:
`HasDerivativeOnInterval.endpointDifference_contains_of_pos` takes one
positive rational cell whose width satisfies the derivative certificate's
step budget and encloses its endpoint difference by the cell width times the
derivative box, widened by twice the requested precision.  This is the exact
finite bridge consumed by partition-level FTC certificates.
`FinitePolynomial.integratedTaylorPrefix_hasDerivativeOnInterval` then closes
this construction under every finite rational coefficient prefix. Its
quantitative `SecantDerivativeBound` is the explicit Taylor-remainder bridge:
only after that bound is supplied does a linear coefficient become an
interval derivative.

The first non-polynomial FTC is exposed in
`ComputableAnalysis.ArctanEffectiveFTC`: the stabilized rectangle integral
of `1 / (1 + x^2)` is equivalent to the geometric arctangent at `1` via
`arctanEffectiveFTCStabilizedIntegral_equiv_arctanGeom_one`. This is the
model for later special functions: define an executable primitive, prove a
finite derivative-bound certificate, stabilize the rectangle evaluator, and
then connect its endpoint value to a geometric or series representation.

The same public normalization is available for the unit exponential:
`uniformExpOnUnitStabilizedIntegral_equiv_powerSeries_one_sub_one` identifies
the effective rectangle integral with the factorial-series value at `1`
minus the exact rational value `1`.  The proof first uses FTC to obtain the
endpoint subtraction, then transports the zero endpoint through the proved
series equivalence; it does not silently identify `exp` with a classical real
number.

The series implementation is connected to this finite algebra without making
an analytic derivative claim. `ExpProofs.powerSeriesTermAtTerms_eq_expCoeff_monomial`
proves that the literal loop's next rational term is `x^N / N!`, while
`ExpProofs.powerSeriesCenterAtTerms_eq_expTaylorPrefix` identifies its finite
center after `N + 1` terms with `FinitePolynomial.expTaylorPrefix N x`.
`FinitePolynomial.expTaylorPrefix_succ` exposes the one-term recurrence, and
`FinitePolynomial.qabs_expCoeff_monomial_le_factorialTailTerm` puts every
term under a common factorial-tail budget on a bounded rational box. Use
these facts before attaching the separately certified geometric tail.
`ExpProofs.uniformExpRaw` now carries out that attachment on `qabs x <= 2`:
its fixed factorial stage is valid, nested, and geometrically shrinking;
`ExpProofs.uniformExpRaw_equiv_expPowerSeries` proves it overlaps the selected
adaptive series evaluator at every common stage. This is the representation
to use when one proof must evaluate both `x` and `x + h` at the same prefix.
`ExpProofs.uniformExpOnUnit` packages the same schedule on `[0,1]` and is
pointwise equivalent to the selected exponential there. Its next finite
prefix has exactly the common center as derivative, while
`ExpProofs.uniformExpTaylorPrefix_secant_error` gives its finite secant error
explicitly. `FinitePolynomial.expTaylorPrefix_secant_error_le_thirty_four`
then proves the single bound `34` for every finite prefix on `|x| <= 2`, and
`ExpProofs.uniformExpTaylorPrefix_secant_error_le_thirty_four` transfers it to
the common schedule. For `h ≠ 0`, choose
`ExpProofs.uniformExpQuotientPrecision h hh n`: its shared tail magnitude is
at most `precisionAtStage n * |h| / 24`. Pair it with
`uniformExpSelfDerivativeStepPrecision`, which spends at most half the
requested tolerance on the `34 |h|` finite error.
`uniformExpSelfDerivativeEvalPrecision` makes this stage choice total, and
`uniformExpCenter_secant_error_le` combines the finite and tail errors before
the interval quotient is assembled. The resulting
`uniformExpOnUnit_hasDerivativeOnInterval` is a full two-sided certificate
`E' = E` on `[0,1]`, and `uniformExpOnUnit_solvesSelfDerivative` adds the
checked exact initial value `E(0) = 1`. It is intentionally a certificate for
the common-prefix evaluator rather than an unproved derivative transfer to
the pointwise-equivalent adaptive evaluator.
The centered chart is now checked as well:
`uniformExpOnSymmetricUnit_hasDerivativeOnInterval` proves the same
certificate on `[-1,1]`, where the endpoint hypothesis gives `|h| <= 2`;
`uniformExpOnSymmetricUnit_solvesSelfDerivative` packages its initial value.
This is the useful local chart for identities that use both signs of the
exponent.

For finite trigonometric work, use
`FinitePolynomial.sineTaylorPrefix_hasDerivativeOnInterval` and
`FinitePolynomial.cosineTaylorPrefix_hasDerivativeOnInterval`. They certify
the actual interval derivative of a finite prefix only: an \(N+1\)-term source
has the \(N\)-term shifted target. The exact dropped-edge calculation is
`taylorPrefixShift_succ_eq_of_coefficientShift`; attach an independent tail
certificate before claiming a derivative for an evaluated sine or cosine raw.

For the tail-enclosed rotation evaluator,
`ComputableAnalysis.RotationCalculus` provides the common factorial schedule
and `ComputableAnalysis.RotationDerivative` supplies its first analytic
derivative certificate. The schedule has
checked literal rational epsilon--delta continuity on `[-2,2]` for both
coordinates: `uniformRotationCosOnTwo_epsilonDeltaContinuous` and
`uniformRotationSinOnTwo_epsilonDeltaContinuous` use the explicit modulus
`delta = eps / 16` together with
`uniformRotationBoxes_widths_shrink_uniform`.  This is already suitable as a
continuity input to a concrete integral construction. It is deliberately not
a derivative transfer. `RotationTaylorBridge` identifies the literal
Peano--Baker centers with the finite formal Taylor prefixes
(`sinePrefix_eq_taylorPrefix` and `cosinePrefix_eq_taylorPrefix`), identifies
the finite shifted sine prefix with the cosine prefix
(`sinePrefixShift_eq_cosinePrefix`), and supplies the fixed-stage rational
secant certificate `uniformRotationSinCenter_secant_error`. Its direct odd
prefix recurrence is majorized by the checked factorial exponential budget,
yielding `uniformRotationSinCenter_secant_error_le_thirty_four`: a single
`34 * |h|` bound on every finite common-stage sine center.
`uniformRotationSinOnTwo_hasDerivativeOnInterval` now spends the remaining
error budget on a stage chosen from `eps * |h| / 48`; together with the
reusable symmetric-box quotient calculation in `IntervalQuotient`, this is a
full two-sided literal certificate `sin' = cos` for the common-prefix
evaluators on `[-2,2]`. The companion is now checked too:
`uniformRotationCosOnTwo_hasDerivativeOnInterval` proves `cos' = -sin`
against `uniformRotationNegSinOnTwo`. A finite cosine prefix drops its final
sine term; Lean bounds that term by its own factorial schedule and evaluates
at the maximum of this edge shift and the divided-tail shift. Neither theorem
silently transfers across a pointwise-equivalent representation.
`RotationInitialValues` also proves the finite initial boxes
`C(0) = 1` and `S(0) = 0` for these exact evaluators, and packages the four
facts as `uniformRotationOnTwo_rotationInitialCertificate`. This is the
checked rotation IVP candidate, still short of its geometric identification or
a continuous vector uniqueness theorem.

Affine reparametrization is available as a total finite chain-rule identity:
`ExactFunction.differenceQuotient_affine_comp_of_step` includes the constant
inner-map case, while `ExactFunction.secant_bracket_affine_endpoint_transport`
handles positive endpoint transport. Use these rational identities as the
starting point for substitution and angle-chart proofs; they do not require a
limit or a completed real function.

At the certificate level, use
`ExactFunction.EffectiveDerivativeExact.affineCompOfPositiveSlope`.  Its
`hbudget` pays for the factor `qabs m`, and its radius hypothesis transports
the step `m*h` into the outer derivative certificate.  Negative slopes are
not silently accepted: the forward-only derivative contract needs a separate
orientation-reversing or two-sided wrapper.

When the outer derivative certificate is already packaged as
`EffectiveFTCExact`, use
`ExactFunction.EffectiveFTCExact.affineCompOfPositiveSlope`.  It reuses the
same finite rectangle substitution identity, so the FTC error bound is
transported at each chosen mesh rather than inferred from a completed
integral.
For sums of certified primitives, use
`ExactFunction.EffectiveFTCExact.addOfCommonSchedule`.  It requires one
shared finite stage schedule and half-budget endpoint certificates; the
finite identity `riemannLeftExact_add` then supplies the exact algebraic
transport.
For a rational coefficient, use
`ExactFunction.EffectiveFTCExact.scaleOfSchedule`.  It reuses the derivative
scaling certificate and transports the finite endpoint error by `qabs c`, with
the inner schedule and budget supplied explicitly.  This is the representative
linear-combination rule; routine coefficient variants should not be duplicated.
When the source certificate's own stage selector is sufficient, the shorter
`ExactFunction.EffectiveFTCExact.scale` closure reuses it automatically; only
the inner precision schedule, derivative radius bound, and scaled error budget
remain as inputs.

The matching integral-side identity is
`ComputableAnalysis.ExactFunction.riemannLeftExact_affine_substitution`. It transports a
positive affine change of variable through the finite left-rectangle fold.
This is the substitution algebra that an effective FTC certificate can later
carry to the nested interval level; it is deliberately not stated as a
general theorem about completed real integrals.
The companion `ComputableAnalysis.riemannLeftExact_affine_closed` gives the
closed rational value of every finite affine fold, including stage zero, and
is useful for regression tests and error estimates.
For a positive stage, `ComputableAnalysis.riemannLeftExact_affine_error_of_pos`
normalizes that formula to the exact integral value plus an explicit
`1 / n` rectangle error.
The nonlinear calibration theorem
`ComputableAnalysis.ExactFunction.ftcErrorExact_square_doubleId_of_pos`
packages the same idea for the primitive `x^2`: its finite FTC error is
exactly `(b-a)^2/n`.
The cubic calibration
`ComputableAnalysis.ExactFunction.ftcErrorExact_cube_threeSquare_unit_of_pos`
exposes the corresponding unit-interval error
`(3*n - 1)/(2*n^2)`.

The first exponential finite-difference brick is also available:
`expTaylorQuadratic x = 1 + x + x^2/2`.
`FinitePolynomial.expTaylorQuadratic_hasDerivativeOnInterval` now proves its
full two-sided interval derivative `1 + x` on every rational subinterval of a
bounded symmetric box; it is assembled by the reusable quantitative
`SecantDerivativeBound` constant/addition/rational-scaling interface.
`ExpProofs.expTaylorQuadratic_forwardDerivativeAtZero` remains the small
specialized forward certificate at zero, whose literal quotient is
`1 + h/2`.  The actual tail-enclosed evaluator has
now crossed the same local gate:
`ExpProofs.expPowerSeriesOnUnit_forwardDerivativeAtZero` proves its forward
derivative at zero is `1`.  Its proof uses the literal public stage-zero
finite sum, whose positive tail and geometric radius are both bounded by
`h^2` on positive half-unit steps.  The companion
`ExpProofs.expPowerSeriesOnUnit_forwardSelfDerivativeAtZero` uses
`expPowerSeries 0` itself as the derivative representative, so it certifies
the precise local identity `D⁺ exp(0) = exp(0) = 1`.  Neither result is a
global `exp' = exp` certificate on an interval.

## How to formalize a familiar integration formula

The project should prove **general** substitution and integration-by-parts
theorems.  It should not maintain a table of antiderivatives.  Once those
theorems exist, an LLM can propose a standard primitive and check it using the
derivative table plus the general endpoint theorem.

Today, use the following plan rather than claiming the result from a matching
derivative alone:

1. define the integrand and proposed primitive as `FunctionOnInterval`s on a
   rational closed interval;
2. prove their domains and validity, then the applicable derivative
   certificate;
3. prove or obtain `IntervalRegularOn` and a concrete
   `Integral.ConstructionFor` for the integrand;
4. prove an `Integral.DefiniteIdentityFor` (or use the ordinary
   `Integral.DefiniteIdentity` when its global raw-function interface fits);
5. derive the displayed endpoint formula from that package.

For a piecewise-monotone integrand, use the separate-primitive API in
`ComputableAnalysis.PrimitivePiecewiseFTC`: the cell areas belong to `F`,
while the endpoint list is evaluated from the proposed primitive `P`.
`Integral.absOnUnit_piecewise_primitiveFTC` is the reference two-cell example.

`FTC.EffectiveFTC` and `FTC.effectiveFTC_definiteIntegralEqualsEndpoint`
describe one checked endpoint-bridge route.  The generic bridge from an
arbitrary `HasDerivativeOnInterval` to that FTC certificate is not yet
available.  `Integral.IntegrationByPartsCertificate` now turns a certified
paired finite-subdivision identity into the standard endpoint-minus-integral
formula through `left_integral_equiv_endpoint_sub_right` (and its symmetric
companion).  An LLM must still construct the two integrals and the common
mesh/corner certificate for its particular functions; that is deliberately
not inferred from a formal product rule alone.

### Same-chart interval addition

`FunctionOnInterval.add F G hlower hupper` is the public interval-level
addition operation.  The equal lower and upper endpoints are explicit because
the two rational charts must describe the same domain.  Its evaluator uses
`QInterval.addInterval`, and `FunctionOnInterval.add_compute` exposes that
stagewise computation.  The validity proof is inherited from
`RealRaw.add_valid`; continuity, derivative certificates, and FTC data remain
separate obligations.

For function-level products, use `FunctionOnInterval.mulOfNonnegBounded`.  It
requires a pointwise rational majorant for each nonnegative factor, which is
the finite condition needed by that representative function chart.  Its
companion `mulOfNonnegBounded_compute` exposes the stagewise product.  At the
raw-real level, arbitrary signed inputs are already closed under the literal
four-corner product; use `RealRaw.mul_valid` and `RealRaw.mul_equiv`.  This
does not remove the need to state local range hypotheses for a particular
interval-valued function or derivative certificate.

When two factor charts are connected by `FunctionOnInterval.Equivalent`,
transport their certified bounded product with
`FunctionOnInterval.equivalent_mulOfNonnegBounded`. The representation graph
stays explicit, while the same rational majorants provide the validity
certificates for the new product chart.

For a Lipschitz--Darboux integral, do not treat the Lipschitz constant as a
canonical choice. If two natural bounds are available, use
`LipschitzDyadic.raw_equiv_of_lipschitz_bounds`; its witness is the common
finite left rectangle sum.

The finite derivative algebra is now exposed as well:
`QInterval.differenceQuotient_addInterval` distributes the interval quotient
over addition, and `intervalNearAtPrecision_addInterval` combines two
near-certificates when the internal precision pays the doubled error budget.
These are the ingredients for the next generic `HasDerivativeOnInterval`
closure theorem; they do not use completeness or a limiting real-number
argument.  That closure theorem is now available as
`HasDerivativeOnInterval.addOfCommonSchedule`.  It requires explicit domain
alignment and equality of the two certificates' stage schedules, then chooses
an internal precision schedule satisfying the doubled-budget inequality.
At the exact rational level, the same transport is available through
`ExactFunction.EffectiveDerivativeExact.add` and
`ExactFunction.EffectiveDerivativeExact.scale`; their inner schedules and
error/radius budgets remain explicit inputs.
Products use `ExactFunction.EffectiveDerivativeExact.mulOfBudget`, whose
explicit obligation includes the quadratic finite corner term; it is a
certificate constructor, not an automatic theorem for arbitrary limits.
When factor and secant magnitudes are already available as rational bounds,
use `product_differenceQuotient_error_le_qabs_of_bounds` to reduce the local
obligation to the two factor-error terms plus the explicit corner budget.
At the interval-evaluator level,
`FunctionOnInterval.mulOfNonnegBounded_compute_width_le` now supplies the
finite product modulus
`width(FG) <= BF * width(G) + BG * width(F)` under nonnegative pointwise
bounds.  This is the box-level input needed by a future interval product-rule
constructor; it does not itself assert a derivative or a limiting product.
The corresponding raw-real theorem is
`RealRaw.mul_width_le_of_nonneg_bounded`; use it when the factor boxes have
already been packaged as `RealRaw` values.
The concrete `sin(pi*x)^2` evaluator uses this interface through
`sinPiSquareOnHalf_compute_width_le`, giving the specialized bound
`width(sin^2) <= 2 * width(sin)` on `[0, 1/2]`.
The scheduled wrapper transports the same estimate through its explicit stage
map via `sinPiSquareOnHalfScheduled_compute_width_le`; this is the form to
use when assembling a scheduled integral certificate.
At the finite integration layer,
`dyadicPublicSquareLeftSum_width_le_of_stage` folds the sample bounds into
the rectangle-sum modulus, and
`dyadicPublicSquareLeftSum_width_le_of_sine_stage` specializes it to a sine
width budget. The latter is the shrinking-width bridge for the public
`sin(pi*x)^2` candidate.
When the sine evaluator is supplied with `IntervalRegularOn`,
`dyadicPublicSquareLeftSum_width_le_of_sine_regular` derives the uniform
bound `width <= 1/(n+1)` by applying the interval contract to degenerate
rational cells.
The resulting finite algorithm is packaged as
`dyadicPublicSquareIntegralRaw`, with
`dyadicPublicSquareIntegralRaw_widths_shrink` proving its width modulus. Its
finite orderedness companion `dyadicPublicSquareLeftSum_ordered` follows
directly from valid square samples and the nonnegative mesh.  Thus the
remaining raw-validity obligation is specifically cross-stage nesting, not
pointwise interval ordering.
`RealRaw.Valid` and equivalence remain separate witness obligations; the
construction deliberately does not infer cross-stage nesting from shrinking
alone.
The companion stabilization interface is
`dyadicPublicSquareIntegralRaw_stabilized`: supplying sine regularity, anchor
validity, and the public-candidate/anchor equivalence yields validity and
value transport through
`dyadicPublicSquareIntegralRaw_stabilized_valid_of_overlap` and
`dyadicPublicSquareIntegralRaw_stabilized_equiv_value_of_anchor`.

### Increasing pieces: start with the literal finite stage

For an arbitrary `IntervalRegularOn F`, use
`Integral.intervalRegularDarbouxRange` for the common image box of a cell and
`Integral.intervalRegularDarbouxStage` for its finite uniform-partition sum.
The theorem
`Integral.intervalRegularDarbouxStage_width_le_of_uniform_input_budget` gives
the explicit `(b-a)/(prec+1)` width bound once the mesh is below the input
modulus.  This is a general finite quadrature candidate, not yet a universal
integrability theorem: cross-stage nesting remains a separate certificate
obligation before constructing a `RealRaw` integral.
The companion
`Integral.intervalRegularDarbouxStage_width_nonneg_of_uniform_input_budget`
discharges the sign of the finite interval width from the same mesh condition;
callers should not repeat this routine cell-fold proof.

When those coherence facts are available, package them in
`Integral.IntervalRegularDarbouxSchedule`. Its orderedness, nesting, and
shrinking-width fields are exactly the remaining proof obligations;
`Integral.intervalRegularDarbouxScheduleRaw_valid` proves the resulting raw
value valid, and
`Integral.intervalRegularDarbouxScheduleConstructionFor` exposes it through
the ordinary integral interface. This is the preferred route for a new
non-monotone function with an explicit finite schedule.
The routine mesh obligation can be discharged by
`Integral.intervalRegularAutomaticPieces_input_budget` after supplying a
natural upper bound for the rational interval length; the corresponding
`intervalRegularAutomaticPieces_pos` theorem supplies positivity.
`IntervalRegularDarbouxSchedule.ofAutomaticPieces` packages this automatic
choice directly, deriving width nonnegativity as well and leaving only the
explicit precision-budget and substantive stage-coherence proofs to the
caller. `intervalRegularDarbouxSchedule_widths_shrink_of_budget` turns the
precision budget into the required eventual-width certificate. Use
`IntervalRegularDarbouxSchedule.ofAutomaticLinearPrecision` when the natural
stage choice is `evalPrecision n = n`; it leaves only the cross-stage nesting
certificate.
`intervalRegularDarbouxScheduleIntegralFor` and its `_valid` theorem as the
public raw integral endpoint.

If a single global unit-chart Lipschitz estimate is being reused on a piece,
use `IntervalRegularOn.of_lipschitzOnUnitSubinterval`. It transports the
estimate and constructs the cell evaluator in one step, so a piecewise proof
does not duplicate the interval enclosure or its precision budget.

For a nondecreasing `FunctionOnInterval F`,
`Integral.nondecreasingDarbouxRange F P k hk prec` is the endpoint box for
the `k`th rational cell of `P`, and
`Integral.nondecreasingDarbouxStage F P prec` folds those width-scaled boxes.
`Integral.nondecreasingDarbouxDyadicStage F hinterval evalPrecision n` is the
literal `2^n`-cell instance used by the blueprint pseudocode.  The theorem
`nondecreasingDarbouxRange_width_nonneg` proves the one finite fact supplied
by weak monotonicity: each endpoint range is ordered.

This API is deliberately *not* a universal integrability result.  To publish
the stage sequence as a `RealRaw`, the particular function still supplies
interval regularity, compatible stage choices, and an explicit bound making
the finite bracket width smaller than any requested rational epsilon.  This
keeps the computation, its validity proof, and its endpoint identity visibly
separate.

### Non-rational turns in a finite monotone decomposition

Do not make a non-rational turn a distinguished kind of integral.  For every
turn in a supplied finite monotone decomposition, use an
`Integral.TurningPointBracket`: its raw boxes expose rational endpoints
`[ell_n, r_n]`.  Evaluate every monotone tail at the same stage and add one
middle box `(r_n - ell_n) * B` for each unresolved gap.  The one-bracket helper
`Integral.TurningBracketIntegralCandidate` proves that one gap's width
vanishes; the general algorithm repeats that finite calculation. Its legacy
Lean implementation name is `SingleTurnIntegralCandidate`.

`Integral.FinitePiecewiseStageAssembly` now performs the finite arithmetic
step: it sums all supplied monotone-piece and gap boxes at one stage, proves
the combined width nonnegative, and gives a finite error-budget proof that it
shrinks.  It deliberately does not infer the individual boxes or their
semantic coverage from a function name.
When every input box has a common bound `B_n`, the checked theorem
`finiteStageSum_width_le_length_mul` gives the explicit aggregate bound
`number_of_boxes * B_n`.

The normalized-sinc illustration uses the first positive solution of
`tan(pi*t) = pi*t`, with a decreasing left tail and increasing right tail.
It is not yet a Lean instance: the project still needs certified sine/tangent
sign boxes and their rational bisection schedule.

This is deliberately a per-function workflow.  A completion certificate for
each assembled finite stage remains the proof obligation that its boxes
enclose the function's intended integral representative.  The current
one-bracket API calls this `TurningBracketIntegralCompletion` (implemented by
the legacy `SingleTurnIntegralCompletion`).  It does not turn every bounded
or continuous interval function into an integral.

For the equal-dyadic nested-radical sine route, the candidate integral is
already a shrinking rational-box algorithm.  The first three finite anchors
`dyadicNestedRadicalLeftSum_zero_overlaps_stieltjes` and
`dyadicNestedRadicalLeftSum_one_overlaps_stieltjes` and
`dyadicNestedRadicalLeftSum_two_overlaps_stieltjes` check its first three
depths against the independent Stieltjes evaluator.  The unresolved obligation is
the all-depth half-angle certificate family in `SinPiIntegral.lean`. Once those
canonical rational boxes are supplied, the direct adapter
`dyadicNestedRadical_sample_overlap_of_canonical_halfAngle_certificate_family`
assembles the parity cases without requiring equality between the public
circle evaluator and the nested-radical evaluator.

The proof obligation is packaged as
`SinPiIntegral.DyadicCanonicalCertificateFamily`: its zero endpoint
equivalence and positive-sample, all-precision certificate family convert via
`DyadicCanonicalCertificateFamily.toWitnessFamily` into the executable search
schedule consumed by the public integral theorem. This separates the
geometric existence proof from the evaluator and makes the remaining theorem
explicit rather than hidden in a large argument.
The candidate side now also exposes
`dyadicNestedRadicalSampleRaw_widths_shrink` and
`dyadicNestedRadicalSampleRaw_stabilized`: once the semantic overlap for one
sample is proved, prefix stabilization supplies a valid public raw without
silently assuming that the raw nested-radical boxes are cross-stage nested.
`ArctanSinPiConstruction.dyadicNestedRadicalSampleRaw_stabilized_equiv`
connects that stabilized candidate to the public sine sample when the
all-precision witness schedule is supplied.
The lower-level theorem
`SinPiTransportSubgoals.exists_dyadic_tangent_witness_search_of_overlap_family`
now exposes the finite boundary precisely: once an all-depth overlap family
is proved, positive nested-radical width automatically yields a successful
rational search at every precision.  No density or completeness principle is
smuggled into the search step.

The square analogue follows the same pattern. Use
`SinPiSquareFTC.dyadicPublicSquareLeftSum_overlap_of_sample_overlaps` for the
finite weighted-fold transport, and
`SinPiSquareFTC.dyadicPublicSquareLeftSum_overlap_of_canonical_search_family`
when each dyadic sample has a successful finite tangent-box search. This keeps
the global theorem generic and leaves only the genuinely new work—the local
search certificate at each sample.
The higher-level theorem
`SinPiSquareFTC.dyadicPublicSquareLeftSum_overlap_of_halfAngle_certificate_family`
connects this directly to the existing canonical half-angle certificate API.
An even more geometric entry point is
`SinPiSquareFTC.dyadicPublicSquareLeftSum_overlap_of_rational_circle_overlap_family`:
it reduces the positive samples to rational-circle image overlap and handles
the zero endpoint separately.

The public-to-anchor step is intentionally stronger than chaining overlaps.
`SinPiSquareFTC.DyadicPublicSquareTangentTransportWitness` asks for a
stagewise containment of the nested square table inside the public square
table, together with the nested-table/tangent common witness.  Its
`to_public_overlap` and `to_public_equiv` theorems then transport the direct
public candidate to the tangent anchor using only rational interval
inequalities.  This is the remaining geometric certificate for the public
sin² integral; no transitivity of overlap is assumed.
The weaker and more natural direct interface is
`SinPiSquareFTC.DyadicPublicSquareTangentSharedWitness`: one rational witness
is required to lie in all three stage intervals.  It yields the same public
equivalence and stabilized-value theorem without requiring containment.
With sine regularity, `DyadicPublicSquareTangentSharedWitness.stabilized_valid`
also exposes the stabilized public computation as a valid `RealRaw`; the
un-stabilized candidate need not itself be nested.
Once the tangent anchor has its quarter-value certificate, the companion
`DyadicPublicSquareTangentTransportWitness.stabilized_equiv_value` theorem
passes that value through the public prefix-stabilized computation.
The two calculus routes can now be compared directly:
`SinPiSquareEffectiveFTCData.integral_equiv_public_stabilized` transports an
effective-FTC integral representation to the stabilized public square
representation, provided both routes carry their explicit quarter-value
certificates.  This is representation transport, not a new completeness
axiom.
The named structure
`SinPiSquareFTC.DyadicSquareCircleOverlapFamily` packages those two fields,
and `to_square_sum_overlap` is the downstream entry point.
Its constructor
`DyadicSquareCircleOverlapFamily.of_halfAngle_certificate_family` translates
the existing canonical half-angle certificate family into this interface.
When a geometric proof is naturally indexed by evaluator precision, use
`canonical_dyadic_halfAngle_certificate_family_of_precision_family` to select
native precision and then
`DyadicSquareCircleOverlapFamily.of_precision_halfAngle_certificate_family`.
The shared branch family feeds the same interface directly through
`DyadicSquareCircleOverlapFamily.of_branch_certificate_family`, so the square
transport reuses the sine sample proof rather than duplicating it.
This is only an index bridge: it adds no completeness or limiting argument.
The normalized square product currently has explicit regression overlaps at
stages 0, 1, and 2; the uniform all-stage witness remains the proof boundary.
The theorem-facing shortcut is
`ArctanSinPiConstruction.halfIntegral_equiv_reciprocalPi_of_canonical_certificate_family`.
The branch-certificate route exposes the same result in rational-circle box
form through `DyadicNestedRadicalBranchCertificateFamily.rational_circle_overlap`.
Its packaged integral transport is
`ArctanSinPiConstruction.halfIntegral_equiv_of_branch_certificate_family`.
For the squared-sine construction, use
`NestedRadicalSquareIntegralConstructionSubgoal.of_branch_certificate_family`:
it reuses that same family at the evaluator precision and produces the
standard equal-plan sample-overlap contract.
The endpoint-value composition is
`ArctanSinPiConstruction.halfIntegral_equiv_reciprocalPi_of_branch_certificate_family`.
The same branch family now feeds the squared-sine fold through
`dyadicPublicSquareLeftSum_overlap_of_branch_certificate_family`; this reuses
the sine overlap proof rather than duplicating geometric witness work.
For proofs that organize data as `precision -> depth -> sample`, the direct
transport entry point is
`ArctanSinPiConstruction.halfIntegral_equiv_of_precision_first_certificate_family`.

One useful fully scoped exception is the unit arctangent triangle route in
`Logarithm.lean`.  Its public name is `arctan.integral.triangle` (implemented
by `Logarithm.arctanIntegralTriangle`), a certified monotone construction for
the public `arctan.integral.rectangle` function on `[0,1]`; its runtime is the
explicit rational triangle mesh, exposed by
`arctanIntegralTriangle_compute_eq`.  The theorem
`arctanIntegralTriangle_add_logKernelIntegral_equiv_productIntegral` compares
that construction plus the `x/(1+x^2)` strip with the independently certified
product-FTC integral.  `Logarithm.piTriangleLogReciprocalIntegral` then gives
the natural endpoint formula with `∫₁² 1/t dt`, and its theorem
`piTriangleLogReciprocalIntegral_equiv_four_coordinateTimesArctanForwardTwoStageMonotoneIntegral`
is the direct product-FTC bridge.  Use these only on this supplied unit
branch; they are not general Fubini, integral-additivity, or
integration-by-parts rules.

## Exponentials, logarithms, and trigonometry

`ElementaryFunctions.lean` is the map of the desired identification route
(the relevant declarations live in the `exp` namespace):

- `exp.PositiveRealRaw.natPow` implements repeated multiplication for a
  positive base;
- `exp.RationalPowerExtension` is the interface for rational exponents;
- `exp.RationalPowerExtension.ContinuousInExponent` asks for rational
  epsilon--delta continuity in the exponent;
- `exp.ExponentialFunction` and
  `exp.ExponentialFunction.SolvesSelfDerivativeOn` record the intended
  analytic characterization; and
- `exp.LogIntegralInverseBranch` records the inverse-logarithmic-integral
  route.

These are mostly interfaces and comparison targets. Do not claim that the
repository has proved a general rational-power construction or the full
exp/log equivalence. The common-prefix exponential does now have a local
`HasDerivativeOnInterval` self-derivative certificate.  Scalar uniqueness
uses the checked direct finite-mesh halving closure below, not a
Peano--Baker or Picard argument; the remaining scalar task is to derive its
finite cell estimates from arbitrary derivative certificates.

The inverse-search side now has a concrete warm-stage façade as well:
`ExpProofs.uniformExpOnUnitWarm` is a four-term-shifted common-prefix
evaluator, `uniformExpOnUnitWarm_intervalRegular` proves its ordinary
interval-width contract, and `uniformExpOnUnitWarm_gapAwareSeparation`
supplies monotone gap-dependent output precision. This is a rational
certificate, not a placeholder for a completed inverse. The completed branch
package is `uniformExpOnUnitWarm_gapAwareInvertible`, using the parallel
`GapAwareInvertibleFunctionOnInterval` contract. The older
`InvertibleFunctionOnInterval` remains the right interface for genuinely
uniform separation schedules. The first concrete target package is
`uniformExpOnUnitWarm_one_target`; its exact preimage search is
`uniformExpOnUnitWarm_one_search`, and
`uniformExpOnUnitWarm_one_preimage_equiv_zero` is the finite branch regression
for `log 1 = 0`.  The parameterized family
`uniformExpOnUnitWarm_forward_target` and
`uniformExpOnUnitWarm_forward_search` proves the same exact inverse contract
for every rational source point in `[0,1]`: the target is the computed warm
forward value and the returned source interval is degenerate at that point.
This is a regression family, not yet the general target-driven bisection
algorithm; that algorithm must make certified midpoint decisions using the
gap-aware separation schedule.
As a finite target-driven kernel, `uniformExpCenter_threeHalves_map` and
`uniformExpCenter_threeHalves_certificate` run exact rational midpoint
decisions for target `3/2`; `uniformExpCenter_threeHalves_finite_bisection`
proves the retained bracket and width `2^-k`. The remaining lift is to use
the requested stage and target interval together with the gap-aware precision
schedule, so this finite certificate is not being misrepresented as the full
inverse evaluator.  The generic `FiniteInverseSearchCertificate.toRealRawFamily`
bridge now turns the finite certificate into a valid stage-indexed nested
interval computation; `uniformExpCenter_threeHalves_inverse_valid` and
`uniformExpCenter_threeHalves_inverse_stage_bracket` instantiate that bridge.
`toRealRawFamily` is an alias of the representative `toRealRaw` computation,
so inverse-search clients do not carry two copies of the same bisection
implementation or validity proof.
`uniformExpCenter_threeHalves_output_forward_overlap` proves the important
finite bridge: the corresponding interval-valued exponential cell range
still overlaps the target interval.
The synchronized decision lemmas
`uniformExpOnUnitWarm_midpoint_below_forward_target` and
`uniformExpOnUnitWarm_midpoint_above_forward_target` consume the gap-aware
separation certificate at the same computed target stage.  They are the
analytic kernel for the adaptive iterator; the remaining work is to prove that
the cell-range evaluator used by the bisection kernel inherits these point-box
separations under the chosen schedule.
That transfer is now proved for degenerate midpoint cells by
`uniformExpOnUnitWarm_cellRange_midpoint_below_forward_target` and
`uniformExpOnUnitWarm_cellRange_midpoint_above_forward_target`: the public
cell-range evaluator reduces to the same finite box when its endpoints agree.
Their `_at_stage` variants prove the schedule rule explicitly: any target box
stage dominating the gap-dependent midpoint stage preserves the strict side
decision by nested interval containment.
The finite schedule bookkeeping is exposed by `finiteNatMax`,
`uniformExpGapPrecisionAt`, and `uniformExpGapPrecisionMax`; the theorem
`uniformExpGapPrecisionMax_dominates` proves that every listed midpoint demand
is covered by the computable maximum.  This is the finite construction to use
when assembling a target-specific schedule.
The concrete grid constructors `dyadicMidpointGrid` and
`dyadicMidpointGridUpTo`, together with `uniformExpRationalTargetStage`,
produce a monotone, cofinal target-stage schedule that dominates every
listed dyadic midpoint demand.  `uniformExpOnUnitWarm_oneThird_target`
instantiates that schedule as a valid forward target for the representative
source value `1/3`; its explicit dominance certificate is
`uniformExpOnUnitWarm_oneThird_target_stage_dominates`.
The arithmetic bridge is now explicit: `dyadicCell` describes a standard
dyadic subinterval, `dyadicCell_left_child` and
`dyadicCell_right_child` identify its two children, and
`dyadicCell_subinterval` certifies that the cell stays in `[0,1]`; finally,
`dyadicCell_midpoint_mem_grid_upTo` proves that every canonical-cell midpoint
is among the finitely listed target demands.
The two transport lemmas
`gapAwareTargetBisectionStep_dyadicCell_of_below` and
`gapAwareTargetBisectionStep_dyadicCell_of_above` now turn a strict midpoint
decision into the exact next dyadic cell, including its new index.
The predicate `gapAwareTargetBisectionStrictDecision` records both the strict
side test and, for the upper-side branch, the fact that the lower-side test
failed.  Under these finite certificates,
`gapAwareTargetBisectionScheduledIterate_dyadicCell` inductively proves that
the entire scheduled iterate is a canonical dyadic cell at every stage.
The companion theorem
`gapAwareTargetBisectionScheduledIterate_width_eq_div_pow_of_strictly_decided`
converts the same strict certificates into the exact width law
`I.width / 2^n`.
For the exponential evaluator, the scheduled-stage transport lemmas
`uniformExpOnUnitWarm_cellRange_midpoint_below_forward_target_at_scheduled_stage`
and its `above` counterpart carry a strict separation certificate from the
minimal gap-dependent precision to the larger target schedule, using nested
finite boxes.
The first target-facing cell certificate,
`uniformExpOnUnitWarm_dyadicCell_strict_below_forward_target`, applies this
transport to a dyadic cell whose midpoint lies below the rational source.
The symmetric `...strict_above_forward_target` theorem handles the other
branch.  Its companion
`uniformExpOnUnitWarm_dyadicCell_below_test_false_of_above` proves that the
failed below-test follows automatically from the two ordered finite boxes;
`...strict_above_forward_target_auto` packages that contradiction into the
same target-facing certificate without an extra hypothesis.
The concrete wrappers `uniformExpOnUnitWarm_dyadicCell_strict_below_oneThird`
and `...strict_above_oneThird` instantiate these certificates at the rational
source (1/3).  The theorem
`uniformExpOnUnitWarm_oneThird_target_compute_eq_forward` identifies the
published scheduled target with the same forward box at its selected stage.
The stage-transport certificates
`uniformExpOnUnitWarm_oneThird_target_strict_below_at_stage` and
`...strict_above_at_stage` carry those decisions to a finer target box.
Finally, `uniformExpOnUnitWarm_oneThird_scheduled_iterate_dyadicCell` proves
by finite induction that every scheduled bisection iterate up to the target
stage is a canonical dyadic cell; `dyadicCell_midpoint_ne_oneThird` supplies
the elementary odd/even obstruction to an ambiguous midpoint.
The companion `uniformExpOnUnitWarm_oneThird_scheduled_iterate_width` reduces
the convergence claim to the explicit rational identity
`width = 1 / 2^n`, with no appeal to completeness.
The endpoint lemmas `dyadicCell_left_endpoint_ne_oneThird` and
`dyadicCell_right_endpoint_ne_oneThird` make the (1/3) containment strict;
their proof is the finite divisibility fact that (3\nmid 2^n).
The reusable calculus lemmas
`gapAwareTargetBisectionScheduledIterate_mem_of_oriented` and
`...scheduled_iterate_nested` separate source containment from target-specific
certificates and record the fixed-target nesting law.  The one-third oriented
certificate is the bridge to the target-varying inverse wrapper.  The new
`dyadicCell_nested_of_strict_contains` lemma supplies the missing bridge: two
strict dyadic cells containing 1/3 are nested even when their target boxes
come from different stages.  Thus
`uniformExpOnUnitWarm_oneThird_bisection_compute_valid` packages the actual
stage-dependent bisection computation as a `RealRaw.ValidCompute`, with exact
geometric width `1 / 2^n` and no completeness axiom.
The companion `...compute_subinterval` and `...value_overlaps` lemmas verify
the interval evaluator against the target box at every requested stage; the
resulting `...oneThird_bisection_search` is a complete concrete
`GapAwareInverseBisectionSearch` certificate.
The public `FiniteGapAwareInverseSearch` module supplies the reusable
plan-to-search adapters, so later inverse branches need only provide their
finite decisions, nesting, width, and overlap certificates.
If a branch already exposes a fixed-gap `EffectiveInverseSeparation`, use
`EffectiveInverseSeparation.toGapAware` with a provider-specific reindexing
schedule and prove the single rational gap inequality required by that
schedule.  This transports the separation certificate without introducing a
classical inverse or a completed real.

Formalization scope is by mechanism, not by exhaustive enumeration.  One
representative function is enough when another function uses the same certified
evaluator, interval nesting, subdivision, or piecewise argument.  Routine
variants should reuse the existing theorem; a function with finitely many
pieces, such as `|x|`, should be handled by splitting the integral into the
corresponding subintegrals.  Add a new formalization only when it introduces a
new computational or proof mechanism.

The reusable `gapAwareTargetBisectionStep` is deliberately conservative. It
keeps a rational parent interval whenever the computed image box overlaps the
target box, and discards a half only after strict finite separation. Its
orderedness and subinterval theorems are proved in `Calculus.lean`. The
remaining adaptive inverse obligation is therefore explicit: its precision
schedule must eventually resolve ambiguous midpoint cases.
The proof-carrying iterators `gapAwareTargetBisectionIterateWithProof` and
`gapAwareTargetBisectionIterate` now package this finite schedule layer; every
stage remains in the original branch and has width no larger than the initial
interval. They intentionally do not claim geometric shrinkage when a midpoint
remains unresolved.
The scheduled iterators `gapAwareTargetBisectionScheduledIterateWithProof`
and `gapAwareTargetBisectionScheduledIterate` make evaluator precision an
explicit independent schedule. Their subinterval and width theorems hold
without a convergence-rate assumption; when a supplied decision schedule
proves every midpoint strict,
`gapAwareTargetBisectionScheduledIterate_width_eq_div_pow_of_decided`
recovers the exact geometric width law.
The midpoint image is named explicitly by
`gapAwareTargetBisectionMidpointRange`; the branch lemmas
`gapAwareTargetBisectionStep_of_below` and
`gapAwareTargetBisectionStep_of_above` expose the two strict decisions as
equalities with the corresponding child interval.  These are the interfaces
used to transport dyadic-cell invariants through bisection.
The warm exponential branch now includes three executable target-`3/2`
midpoint regressions. At precision stage `4` they produce
`[0,1/2]`, `[1/4,1/2]`, and `[3/8,1/2]` in succession, all by finite rational
interval decisions.
The fixed-precision iterator
`gapAwareTargetBisectionFixedIterateWithProof` packages this same recursion;
the theorem `uniformExpOnUnitWarm_three_halves_fixed_precision_trace` checks
that three iterations at precision `4` produce `[3/8,1/2]` directly.
`gapAwareTargetBisectionFixedDecision` and
`gapAwareTargetBisectionFixedIterate_width_eq_div_pow_of_decided` formalize
the progress boundary: strict midpoint separation at every stage yields the
exact width law `initial_width / 2^n`.
The warm exponential example supplies the first three decision certificates
for target `3/2`, and derives the `1/8` width result through that generic
theorem rather than through a separate arithmetic trace.

The arctangent branch has the same representation split. The lightweight
scheduled rectangle core in `ArctanScheduledCore.lean` exposes the staged raw
evaluator, its width budget, validity, and equivalence to the geometric
arctangent without importing inverse-search regularity. The heavier
`ArctanScheduledRegular.lean` layer adds interval regularity, monotonicity,
effective separation, and an `InvertibleFunctionOnInterval` package. Its
`arctanScheduledRectangleOnUnit_equivalent_geometric_branch` theorem connects
that precision-friendly evaluator to the geometric arctangent used by the
circle chapter.

For a direct scalar uniqueness proof, make one finite short-block sweep an
instance of `ScalarODE.ShortBlockMeshSweep`: telescope the cell estimates to
`next <= length * previous + residual`, choose `length <= 1/4`, and spend at
most `previous/4` on the residual. The checked theorem `next_le_half`
produces the dyadic contraction. Feed the sweep sequence to
`DirectMeshHalvingCertificate.ofShortBlockSweeps`; its `error_eq_zero`
theorem is preceded by `error_le_eps`, which chooses a concrete refinement
count for any proposed rational error. This is the intended hand proof of
scalar `f' = f` uniqueness.

The cellwise form is now executable too. Use
`FiniteMeshDifferenceBound` with rational endpoint envelopes `state j`,
`state 0 = 0`, and a certified bound for each increment
`state (j+1) - state j`. `FiniteMesh.sumUpTo_increments` proves the literal
finite telescoping identity, and `toShortBlockMeshSweep` turns the total
length/residual budgets into the contraction certificate. The open analytic
work is therefore exactly to derive those finite increment bounds from
`HasDerivativeOnInterval`, at the chosen mesh precision.
The arithmetic template
`ScalarODE.ShortBlockMeshSweep.canonical` and its theorem
`canonical_next_le_half` provide the exact quarter-plus-quarter budget that a
concrete derivative certificate must reproduce.

The literal power-series computation itself is now fully certified at every
rational input: `ExpProofs.expPowerSeries_valid x` proves the raw boxes for
`expPowerSeries x` valid, and `ExpProofs.expPowerSeriesRate x` records the
explicit geometric bound
`width <= 4 * |first omitted term at stage 0| * (1/2)^n`.  This is a
rational finite-sum/tail certificate, including nesting.  It is now packaged
as the total `ExpProofs.expPowerSeriesFunction : PartialRealFunRaw`, with
`ExpProofs.expPowerSeriesOnInterval a b` supplying its valid restriction to a
rational closed interval.  If the interval contains zero,
`ExpProofs.expPowerSeriesOnInterval_zero_initial_value` supplies exactly the
initial-value equivalence required by `SolvesSelfDerivativeOnInterval`.
This representation layer is deliberately still not a derivative theorem. At
the constant input `1`, it is now proved
equivalent to compound interest; the inverse-logarithmic construction remains
a separate open bridge.

There is one local derivative theorem for that representation:
`ExpProofs.expPowerSeriesOnUnit_forwardDerivativeAtZero` proves the full
power-series evaluator has forward derivative `1` at zero, while
`ExpProofs.expPowerSeriesOnUnit_forwardSelfDerivativeAtZero` proves the
equivalent statement with `expPowerSeries 0` itself as derivative data.  Both
are deliberately kept distinct from the still-open interval self-derivative
certificate needed by `SolvesSelfDerivativeOnInterval`.

When using `SelfDerivativeInitialValueUnique`, provide both pieces of common
initial data explicitly: equality of the rational initial coordinates and a
`RealRaw.Equiv` proof for their certified initial values.  The differential
equation alone does not identify two solutions with different initial values.

The two concrete finite evaluators do now have a checked initial condition.
`ExpProofs.expPowerSeries_zero_compute_eq n` identifies the series box at
zero with the point interval `1` at every stage, while
`ExpProofs.expEuler_zero_equiv_one` proves that the repeated-multiplication
box at zero overlaps that same rational point interval at every stage.  The
latter retains its deliberate displayed radius.  These are finite loop
calculations and establish `exp(0) = 1`; they do not establish a derivative
or agreement of the evaluators at nonzero input.

The finite algebra needed for the nonzero comparison is now available as a
small readable API: `fallingFactorialRat`, `eulerBinomialTerm`, and
`eulerBinomialPrefix`.  The checked theorem
`euler_binomial_prefix_nat_expansion m x` is the rational finite identity
`prefix (m : Rat) x (m + 1) = (1 + x)^m`.  At `x = 1 / m`, it gives the exact
factorial-coordinate expansion of the literal Euler product. Lean now proves
the quadratic coefficient-loss estimate, sums it to a `3/m` prefix budget,
and compares it with the factorial tail and nested Euler radius. The resulting
theorem `ePowerSeries_equiv_eCompoundInterest` is the constant-level
series/compound equivalence; function-level and inverse-logarithm agreements
remain open.

There is, however, one fully certified constant-level exponential handle that
is useful today.  `ExpProofs.e : Real` has the sharp compound-interest
enclosure as its preferred representation and
`ExpProofs.eRepeatedMultiplicationRepresentation` as an alternate
representation.  The latter is a direct nested evaluator: stage `n` computes
the single rational power `(1 + 1/(n+1)^2)^((n+1)^2)` and uses radius
`8/(n+1)`, giving exact width `16/(n+1)`.  The compound-interest boxes are
used only in its validity/equivalence proof, never at runtime.  The older
prefix-stabilized evaluator remains available separately for diagnostics.
The same abstract handle now also stores `ePowerSeries`; its direct rational
binomial/tail proof is `ePowerSeries_equiv_eCompoundInterest`, and
`ePowerSeriesRepresentation` makes that representation explicit.
The preferred compound-interest representative is also the checked positive
base `ExpProofs.ePositive`: every lower endpoint is at least `2`, and its
literal natural powers `ExpProofs.eNaturalPower n` are valid with interval
bounds `2^n <= lo <= hi <= 4^n`. This is ready to be supplied to a future
`exp.RationalPowerExtension`; it is not that extension.
The relevant checked facts are:

```lean
import ComputableAnalysis.ExpProofs

open ComputableAnalysis

#check ExpProofs.e
#check ExpProofs.expPowerSeries_valid
#check ExpProofs.expPowerSeriesRate
#check ExpProofs.expPowerSeriesFunction
#check ExpProofs.expPowerSeriesFunction_valid
#check ExpProofs.expPowerSeriesOnInterval
#check ExpProofs.expPowerSeriesFunction_zero_equiv_one
#check ExpProofs.expPowerSeriesOnInterval_zero_initial_value
#check ExpProofs.expPowerSeriesOnUnit_forwardDerivativeAtZero
#check ExpProofs.expPowerSeriesOnUnit_forwardSelfDerivativeAtZero
#check ExpProofs.powerSeriesTermAtTerms_eq_expCoeff_monomial
#check ExpProofs.powerSeriesCenterAtTerms_eq_expTaylorPrefix
#check FinitePolynomial.expTaylorPrefix_succ
#check FinitePolynomial.qabs_expCoeff_monomial_le_factorialTailTerm
#check ExpProofs.uniformExpRaw
#check ExpProofs.uniformExpRaw_valid
#check ExpProofs.uniformExpRaw_equiv_expPowerSeries
#check ExpProofs.uniformExpOnUnit
#check ExpProofs.uniformExpOnUnit_equivalent_expPowerSeriesOnUnit
#check ExpProofs.expTaylorDerivativePrefix_eq_powerSeriesCenterAtTerms
#check ExpProofs.uniformExpTaylorPrefix_secant_error
#check FinitePolynomial.expTaylorPrefixSecantCoefficient_le_thirty_four
#check FinitePolynomial.expTaylorPrefix_secant_error_le_thirty_four
#check ExpProofs.uniformExpTaylorPrefix_secant_error_le_thirty_four
#check ExpProofs.uniformExpQuotientTailTolerance
#check ExpProofs.uniformExpQuotientPrecision
#check ExpProofs.uniformExpTailMagnitude_le_quotientTolerance
#check ExpProofs.uniformExpSelfDerivativeStepPrecision
#check ExpProofs.uniformExpSelfDerivative_finite_error_le_half_precision
#check ExpProofs.expPowerSeries_zero_compute_eq
#check ExpProofs.expPowerSeries_zero_valid
#check ExpProofs.expPowerSeries_zero_equiv_one
#check expTaylorQuadratic
#check FinitePolynomial.taylorPrefixShift_at_zero
#check FinitePolynomial.taylorPrefixShiftAt_at_basepoint
#check FinitePolynomial.taylorPrefix_succ
#check FinitePolynomial.taylorPrefixShift_succ_eq_of_coefficientShift
#check FinitePolynomial.monomialSecantDerivativeBound
#check FinitePolynomial.monomial_hasDerivativeOnInterval
#check FinitePolynomial.cubeSecantDerivativeBound
#check FinitePolynomial.cube_hasDerivativeOnInterval
#check FinitePolynomial.taylorPrefix_hasDerivativeOnInterval
#check FinitePolynomial.taylorPrefixAt_hasDerivativeOnInterval
#check FinitePolynomial.sineTaylorPrefix_hasDerivativeOnInterval
#check FinitePolynomial.cosineTaylorPrefix_hasDerivativeOnInterval
#check FinitePolynomial.SecantDerivativeBound.mul
#check FinitePolynomial.SecantDerivativeBound.mulToHasDerivativeOnInterval
#check HasDerivativeOnInterval.endpointDifference_contains_of_pos
#check HasDerivativeOnInterval.scaleRat
#check HasDerivativeOnInterval.linearCombinationOfCommonSchedule
#check FinitePolynomial.integratedTaylorPrefix_hasDerivativeOnInterval
#check FinitePolynomial.expTaylorQuadratic_hasDerivativeOnInterval
#check ExpProofs.expTaylorQuadratic_forwardDerivativeAtZero
#check ExpProofs.eulerCenter_zero
#check ExpProofs.expEuler_zero_equiv_one
#check ExpProofs.fallingFactorialRat
#check ExpProofs.eulerBinomialTerm
#check ExpProofs.eulerBinomialPrefix
#check ExpProofs.euler_binomial_prefix_nat_expansion
#check ExpProofs.ePowerSeries_equiv_eEulerNested
#check ExpProofs.ePowerSeries_equiv_eCompoundInterest
#check ExpProofs.ePositive
#check ExpProofs.eNaturalPower_valid
#check ExpProofs.eNaturalPower_lower_bound
#check ExpProofs.eNaturalPower_upper_bound
#check ScalarODE.DirectMeshHalvingCertificate
#check ScalarODE.FiniteMesh.sumUpTo
#check ScalarODE.FiniteMesh.sumUpTo_increments
#check ScalarODE.FiniteMeshDifferenceBound
#check ScalarODE.FiniteMeshDifferenceBound.toShortBlockMeshSweep
#check ScalarODE.FiniteMeshDifferenceBound.next_le_half
#check ScalarODE.ShortBlockMeshSweep
#check ScalarODE.ShortBlockMeshSweep.next_le_half
#check ScalarODE.DirectMeshHalvingCertificate.ofShortBlockSweeps
#check ScalarODE.DirectMeshHalvingCertificate.bound_le_geometric
#check ScalarODE.DirectMeshHalvingCertificate.error_le_eps
#check ScalarODE.DirectMeshHalvingCertificate.error_eq_zero
#check ScalarODE.SelfDerivativeDirectMeshComparison
#check ScalarODE.selfDerivativeInitialValueUnique_of_directMesh
#check exp.powerSeries_equiv_logIntegralInverse_on_interval_of_directMesh
#check ExpProofs.eCompoundInterestRepresentation
#check ExpProofs.eRepeatedMultiplicationRepresentation
#check ExpProofs.eEulerNested_valid
#check ExpProofs.eEulerNested_equiv_eCompoundInterest
#check ExpProofs.eEulerStabilized_valid
#check ExpProofs.eEulerStabilized_equiv_eCompoundInterest
#check ExpProofs.ePowerSeries_mem_eCertified_alternatives
#check ExpProofs.ePowerSeriesRepresentation
```

This certifies both repeated multiplication and the factorial power series as
representations of the same abstract value `e`.  Keep that constant-level
agreement, the checked local self-represented forward derivative at zero, and
the still-open global derivative/ODE certificate distinct.

```lean
import ComputableAnalysis.RotationSeries

open ComputableAnalysis

#check RotationSeries.rotationCenter_eq_expPartial
#check RotationSeries.rotationExpRaw
#check RotationSeries.rotationExpRaw_valid
#check RotationSeries.rotationExpRaw_width_le_geometric
#check RotationSeries.rotationCosRaw_valid
#check RotationSeries.rotationSinRaw_valid
#check RotationSeries.rotationCosRaw_compute
#check RotationSeries.rotationSinRaw_compute
#check RotationSeries.uniformRotationCenter_input_lipschitz
#check RotationSeries.uniformRotationBox_future_contained_expand_of_input_near
#check RotationSeries.uniformRotationCosOnTwo_zero_equiv_one
#check RotationSeries.uniformRotationSinOnTwo_zero_equiv_zero
#check RotationSeries.uniformRotationNegSinOnTwo_equiv_neg_sin
#check RotationSeries.RotationDerivativeInitialCertificate
#check RotationSeries.uniformRotationOnTwo_rotationInitialCertificate
```

These names expose the certified complex series at rational imaginary inputs.
The uniform schedule adds a finite Lipschitz certificate on `|T| <= 2`, which
is the input-stability ingredient for represented angles. Their real and
imaginary coordinates are still not identified with geometric trigonometry.

```lean
import ComputableAnalysis.RotationLift

open ComputableAnalysis

#check RotationLift.HalfPiInput
#check RotationLift.HalfPiInput.midpoint_qabs_le_two
#check RotationLift.HalfPiInput.rotationCandidate
#check RotationLift.HalfPiInput.rotationRadius
#check RotationLift.HalfPiInput.rotation
#check RotationLift.HalfPiInput.rotation_valid
#check RotationLift.HalfPiInput.rotation_contains_current_candidate
```

`RotationLift` is the represented-input assembly step in isolation.  Supply a
valid nested raw angle with boxes in `[1,2]` and width at most `2/(n+1)`; it
then stabilizes the common rational factorial boxes with the explicit radius
`16 * width`, and proves the result valid.  A particular pi presentation is
an instantiation of this finite certificate, not an extra assumption in the
generic complex proof.

The literal four-corner complex product has finite containment, order,
nesting, and a rational width estimate.  The width schedule is obtained from
the two stage-zero boxes: nested validity keeps all later coordinates within
their explicit rational radii.  Thus general `ComplexRaw.mul` is a valid raw
computation and respects overlap equivalence.

The scalar version is available through the same interval mechanism:

```lean
import ComputableAnalysis.ComplexMultiplication

open ComputableAnalysis

#check RealRaw.mul_compute_ordered
#check RealRaw.mul_compute_nested
#check RealRaw.mul_valid
#check RealRaw.mul_equiv
#check QInterval.inv_of_pos
#check QInterval.inv_overlaps_of_pos
#check QInterval.inv_ordered_of_pos
#check QInterval.inv_width_eq_width_div_product_of_pos
#check QInterval.inv_nested_of_pos
#check RealRaw.positiveInvCompute
#check RealRaw.positiveInv_compute_ordered
#check RealRaw.positiveInv_compute_nested
#check RealRaw.positiveInv_valid
#check RealRaw.positiveInv_equiv_of_stages
#check RealRaw.positiveInv_equiv_of_input
#check RealRaw.positiveInv_mul_self_equiv_one
#check RealRaw.negativeInv
#check RealRaw.negativeInv_valid
#check RealRaw.negativeInv_equiv_of_stages
#check RealRaw.negativeInv_equiv_of_input
#check RealRaw.negativeInv_mul_self_equiv_one
#check RealRaw.divByPositive
#check RealRaw.divByPositive_valid
#check RealRaw.divByPositive_equiv_of_stages
#check RealRaw.divByPositive_equiv_of_inputs
#check RealRaw.divByNegative
#check RealRaw.divByNegative_valid
#check RealRaw.divByNegative_equiv_of_stages
#check RealRaw.divByNegative_equiv_of_inputs
```

These reciprocal lemmas are deliberately finite: they apply after an interval
has been certified strictly positive.  `RealRaw.positiveInv_valid` packages
the resulting separated branch as a shrinking raw real, and
`RealRaw.negativeInv_valid` transports it through negation.  The unrestricted
`HasComputableInv` interface is not used as a substitute for either explicit
branch.

The representation graph remains connected when the certified separation stage
changes: `RealRaw.positiveInv_equiv_of_stages` supplies the equivalence edge
between any two positive reciprocal schedules.

Division is then a certified product: choose a stage where the denominator is
strictly positive or strictly negative, construct its corresponding reciprocal,
and multiply.  The quotient constructor does not accept a denominator that may
cross zero.

Changing the positive separation stage is harmless: the quotient-stage theorem
transports the two products through the reciprocal equivalence and the product
equivalence theorem.

```lean
import ComputableAnalysis.ComplexMultiplication

open ComputableAnalysis

#check QBox.mulRealInterval_contains
#check QBox.mulRealInterval_ordered
#check QBox.mulRealInterval_nested
#check QBox.mul_contains
#check QBox.mul_ordered
#check QBox.mul_nested
#check QBox.mulRealInterval_width_le_of_abs_bounded
#check QBox.mul_width_height_le_of_coordinateBounded
#check QBox.mul_overlaps_of_overlaps
#check ComplexRaw.mul_compute_ordered
#check ComplexRaw.mul_compute_nested
#check ComplexRaw.mul_valid_of_widthsShrink
#check ComplexRaw.mul_valid
#check ComplexRaw.mul_equiv
#check ComplexRaw.qcomplexLeftMul_equiv_mul_ofQComplex
```

To act on a certified complex input by any exact rational complex scalar, use
the affine layer below.  It remains a particularly transparent exact
implementation, even though the general product is now available.

```lean
import ComputableAnalysis.ComplexAffine

open ComputableAnalysis

#check ComplexRaw.mulI
#check ComplexRaw.mulI_valid
#check ComplexRaw.imaginaryAxis
#check ComplexRaw.imaginaryAxis_valid
#check ComplexRaw.imaginaryAxis_compute
#check ComplexRaw.scaleRat_valid
#check ComplexRaw.qcomplexLeftMul
#check ComplexRaw.qcomplexLeftMul_valid
#check ComplexRaw.qcomplexLeftMul_equiv
#check ComplexRaw.cauchyStabilize
#check ComplexRaw.cauchyStabilize_contains_current
#check ComplexRaw.cauchyStabilize_equiv_of_common_candidate
#check ComplexRaw.cauchyStabilize_valid
```

For example, if `piRaw` has a proof `hpi : piRaw.Valid`, then
`ComplexRaw.qcomplexLeftMul_valid { re := 0, im := 1 / 2 } hpi` certifies the
literal exact-scalar action `(i/2) * piRaw`; this agrees with the direct
`imaginaryAxis` coordinate rotation and rational rescaling.  This supplies
the represented input `i*pi/2`, but not a complex exponential algorithm at
represented inputs.

For a direct complex candidate whose stages are not yet nested, use
`ComplexRaw.cauchyStabilize`.  Its proof contract is entirely finite: give
ordered candidate boxes, widths that shrink, a radius schedule that shrinks,
and show that every later candidate is contained in each earlier widened box.
The evaluator is then the finite intersection of the widened prefix; the
later candidate itself witnesses that every such intersection is ordered.  It
is the intended final assembly step for the represented-angle rotation series.

When the selected value is the project pi handle, import
`ComputableAnalysis.PiComplex` and use the named input rather than choosing a
presentation ad hoc:

```lean
import ComputableAnalysis.PiComplex

open ComputableAnalysis

#check PiProofs.pi.imaginaryHalf
#check PiProofs.pi.imaginaryHalf_valid
#check PiProofs.pi.halfPi
#check PiProofs.pi.halfPi_valid
#check PiProofs.pi.halfPi_width_le_two_div_succ
#check PiProofs.pi.halfPi_bounds
#check PiProofs.pi.halfPiRotation
#check PiProofs.pi.halfPiRotation_valid
#check PiProofs.pi.halfPiRotation_contains_current_candidate
#check RotationLift.HalfPiInput.midpoint_sub_le_width_add_width_of_equiv
#check RotationLift.HalfPiInput.crossRadius
#check RotationLift.HalfPiInput.crossRadius_shrinks
#check RotationLift.HalfPiInput.rotationCandidate_sameStage_contained_expand_of_equiv
#check RotationLift.HalfPiInput.rotation_equiv_of_input_equiv
#check RotationLift.HalfPiInput.rationalInput
#check RotationLift.HalfPiInput.rationalInput_rotation_equiv_uniformRotationExpRaw
#check RotationLift.HalfPiInput.rotation_equiv_uniformRotationExpRaw_of_equiv_ofRat
#check PiProofs.pi.halfPi_equiv_geometricHalfPi
#check PiProofs.pi.halfPiRotationCandidate_contained_expand_geometricRotationCandidate
#check PiProofs.pi.geometricRotationCandidate_contained_expand_halfPiRotationCandidate
#check PiProofs.pi.halfPiRotation_equiv_geometricRotation
#check SectorAreaRotation.halfPi
#check SectorAreaRotation.halfPi_bounds
#check SectorAreaRotation.piRaw_equiv_fourArctanGeomOne
#check SectorAreaRotation.imaginaryHalf_equiv_geometricImaginaryHalf
#check SectorAreaRotation.rotation_equiv_geometricRotation
#check PiProofs.pi.halfPiRotation_equiv_sectorAreaRotation
#check PiProofs.pi.imaginaryHalf_equiv_sectorAreaRotationImaginaryHalf
#check PiProofs.pi.sectorAreaPiRaw_equiv_piCircleArea
#check PiProofs.pi.imaginaryHalf_equiv_imaginaryAxis_halfPi
#check PiProofs.pi.imaginaryHalf_equiv_geometricImaginaryHalf
#check PiProofs.pi.imaginaryHalf_equiv_qcomplexLeftMul
#check PiProofs.pi.imaginaryHalf_qcomplexLeftMul_equiv_presentation
#check PiProofs.pi.negativeTwoImaginaryScalar_imaginaryHalf_equiv_piCircleArea
#check PiProofs.pi.negativeTwoImaginaryRaw
#check PiProofs.pi.negativeTwoImaginaryRaw_valid
#check PiProofs.pi.negativeTwoImaginaryRaw_mul_imaginaryHalf_equiv_piCircleArea
#check PiProofs.pi.negativeTwoImaginary_logAtI_equiv_piCircleArea
#check PiProofs.pi.negativeTwoImaginaryRaw_mul_logAtI_equiv_piCircleArea
#check PiProofs.pi.imaginaryHalf_equiv_presentation
```

`halfPi` is a certified raw angle with boxes in `[1,2]`.
`halfPiRotation` is the valid complex raw obtained by
stabilizing the bounded rational factorial rotations at the midpoint of those
boxes. Its explicit input radius is at most `32 / (n + 1)`, and
`halfPiRotation_contains_current_candidate` lets a later geometric
quarter-turn enclosure lift from a direct factorial candidate to that raw.
This is deliberately not yet `exp(i*pi/2) = i`: the missing proof is exactly
the agreement of the factorial rotation with the geometric circle point.

The rational-circle and arctangent code contains useful geometric and
power-series computations, but normalized-angle sine/cosine/tangent special
values remain partly target-level.  Consult the green/orange legend in the
blueprint before relying on one.

For a first-quadrant special value, the central certified interface is
`RationalCircle.GeometricTrig.FirstQuadrantArctanWitness`. It records a
rational slope in `[0,1]` and the one required equation
`arctan.geom(slope) = t*pi/4`. Its checked bridge then returns the exact
stereographic cosine and sine coordinates and their unit-circle identity:

```lean
import ComputableAnalysis.ArctanGeometry

open ComputableAnalysis

#check RationalCircle.GeometricTrig.FirstQuadrantArctanWitness
#check RationalCircle.GeometricTrig.FirstQuadrantArctanWitness.arctan_to_sine_cosine_coordinates
#check ArctanGeometry.arctanGeom_one_valid
#check ArctanGeometry.four_arctanGeom_one_compute_eq_piCircleArea_compute
#check ArctanGeometry.four_arctanGeom_one_equiv_piCircleArea
#check ArctanGeometry.two_arctanGeom_one_compute_eq_quarterTurnRaw_one_compute
#check ArctanGeometry.two_arctanGeom_one_equiv_quarterTurnRaw_one
```

This is why the special-values table colors only its arctangent-witness
column: the displayed sine and cosine entries follow by rational algebra once
that one equation is certified. At present, only the two endpoint witness
equations are fully proved; the non-endpoint rows remain computation-ready
targets until their raw-slope equalities are formalized.

At the nontrivial endpoint,
`two_arctanGeom_one_compute_eq_quarterTurnRaw_one_compute` gives literal
equality of the two rational interval boxes at every stage; its equivalence
corollary records `2 * arctan.geom(1) = pi / 2` as the normalized geometric
quarter turn.  `PiProofs.pi.halfPi_equiv_geometricHalfPi` now transports that
geometric angle to the geometry-only half-angle consumed by the represented
factorial rotation, and
`PiProofs.pi.imaginaryHalf_equiv_geometricImaginaryHalf` does the same after
embedding on the imaginary axis.  The generic theorem
`RotationLift.HalfPiInput.rotation_equiv_of_input_equiv` now transports this
input equivalence through the two separately stabilized factorial rotations;
`PiProofs.pi.halfPiRotation_equiv_geometricRotation` specializes it to the
registry and geometry-only half-angle inputs.  Its finite core bounds
equivalent midpoint samples by the sum of their widths and uses the
corresponding cross enclosure with radius at most `64/(n+1)`.  The remaining
Euler bridge is the identification of that factorial rotation with its
geometric endpoint, not a conversion of representatives.

The lift has a checked rational compatibility law as well:
`RotationLift.HalfPiInput.rationalInput_rotation_equiv_uniformRotationExpRaw`
says that lifting an exact rational angle in `[1,2]` gives the pre-existing
common-schedule rational factorial rotation.  Thus the represented evaluator
extends, rather than replaces, the rational complex exponential algorithm.
The companion theorem
`rotation_equiv_uniformRotationExpRaw_of_equiv_ofRat` makes this independent
of the selected valid raw representative of that rational angle.

The same small geometry module also carries the full-area bridge directly:
`four_arctanGeom_one_compute_eq_piCircleArea_compute` is stagewise equality
of `4 * arctan.geom(1)` with `piCircleArea`, and
`four_arctanGeom_one_equiv_piCircleArea` is its raw-real corollary.  Use
these declarations for the geometric pi route instead of importing the larger
presentation registry merely for that fact.

## Arctangent on the full series chart

The finite-Riemann comparison is now a reusable equality of represented
functions, not only an endpoint fact.  For any rational `x` with `|x| <= 1`,
the following declarations certify `arctan.series(x) ≡ arctan.geom(x)`:

```lean
import ComputableAnalysis.PiProofs

open ComputableAnalysis

#check PiProofs.arctanEqualsGeom_finiteRiemannBridge_on_unit
#check PiProofs.arctanPowerSeriesGeomAgreement_finiteRiemannBridge
```

The finite quadrature proof supplies the nonnegative branch.  The negative
branch is not a fresh integral argument: both raw evaluators are exactly the
endpoint-reversed negation of their evaluation at `-x`, and Lean proves that
reflection at the raw-interval level.  This broadens the arctangent API, but
does not add a ninth pi-scoreboard row.

For rational-circle chord refinements, do not select an exact square root.
The direct evaluator is already certified in
`ComputableAnalysis/CircumferenceBridge.lean`.  Its public endpoints are:

```lean
import ComputableAnalysis.CircumferenceBridge

#check PiProofs.innerChordLowerRefinement
#check PiProofs.piCircumference_valid
#check PiProofs.piCircumference_nonneg_bounded_by_four
#check PiProofs.piCircumferenceDirect
#check PiProofs.piCircumferenceDirect_equiv_piCircleArea
#check PiProofs.piCircumferenceDirect_equiv_piCircumferenceFan
#check PiProofs.pi.circumferenceDirect
#check PiProofs.pi.circumferenceDirect_equiv_circleArea
#check PiProofs.pi.circumferenceDirect_equiv_circumference
```

The proof reduces every stage to rational data.  It uses
`RationalCircle.Stage.secantChordLower` and the curvature lower certificate
for adjacent fine chords, pays their literal bisection widths, checks stages
(1,2,4,8) exactly, and uses a natural-number exponent bound from then on.
Use the public declarations above rather than reproducing that local
margin argument in a downstream proof.  The direct chord path and default
cross-fan views now also have their own raw and representation-level
equivalence theorems; stabilized variants remain regression implementations.

For a nonlinear construction that depends on pi, use the explicitly proved
representation transport rather than treating raw values as equal.  For
example, `Basel.circumferencePiSquaredOverSixRaw_equiv_geometric` proves that
the direct circumference and area versions of `pi^2 / 6` agree.
Consequently `Basel.eulerBasel_circumference_iff_geometric` transfers the
future Basel theorem between those two pi representations without claiming
the zeta-two identity itself.


## Pi as a regression suite, not a target namespace

`PiProofs.PiCoverageBridge` is deliberately a compact list of distinct
end-to-end capability tests.  It currently has eight checked bridges; it is
not a percentage or a catalogue of all certified pi computations.  Consume a
named presentation from the abstract `pi.value : Real` handle when you need a
specific implementation:

```lean
import ComputableAnalysis.PiProofs

open ComputableAnalysis

#check pi.circleArea
#check pi.circumference
#check pi.arctanGeom
#check pi.integrationByParts
#check pi.squareSubstitution
#check pi.squareStieltjes
#check pi.leibniz
#check pi.dirichletBeta
#check pi.machin
#check pi.cauchy
#check pi.symmetricCauchy
#check pi.reciprocalQuartic
#check Real.Representation.equiv
#check pi.representations_equiv
```

For example, `pi.machin` is the one classical series computation
`16 * arctan.series (1/5) - 4 * arctan.series (1/239)`.  Its agreement with
the area presentation is proved, but it does not create a separate coverage
cell: it reuses the same arctangent-series capability already tested by the
Leibniz bridge. `pi.dirichletBeta` records the equally literal formula
`pi = 4 * L(1, chi4)`; its raw evaluator is stagewise the Leibniz alternating
series, so it is a named view rather than another coverage cell. Similarly,
the direct geometric diagnostic
`pi.circumference` and the certified normalizations
`pi.circumferenceStabilized`/`pi.circumferenceReboxed` are alternative views,
not additional points on the scoreboard.  Use
`PiCoverageBridge.equivalent` only when the compact suite itself is what a
test needs; expose the natural integral, series, or geometry theorem in a
downstream result.  When two named checked evaluators themselves must be
compared, use `PiProofs.piPresentation_equiv source target`; it derives their
raw-real equivalence through the certified area presentation, without
pretending that the comparison adds a new calculus capability.
`pi.integrationByParts` is the checked supplied-unit formula using the
literal reciprocal-integral logarithm, with runtime bound `52 / 2^n`; it
supplies one paired-mesh certificate for the checked general rebalancing
theorem, but not the still-open automatic construction of such certificates
or canonical-exp/log transport. `pi.squareSubstitution` is a separate checked
bridge with runtime bound `56 / 2^n`: its raw formula retains the pullback
integral `2 * ∫_0^1 2*x/(1+x*x) dx`, and its agreement with
`pi.integrationByParts` is the finite `t = x*x` substitution certificate.
It is likewise not a general substitution theorem.
`pi.squareStieltjes` is the supplementary direct-mesh view: it evaluates
the stabilized finite Stieltjes sums for the same substitution, then proves
equivalent to `pi.squareSubstitution` and area pi.  It is an executable
algorithmic witness in the primary pi registry, not a ninth coverage bridge.

For the equal-dyadic sine route, the finite candidate sum now has an explicit
ordered-interval theorem:
`SinPiIntegral.dyadicNestedRadicalLeftSum_width_nonneg`. If a geometric or
Stieltjes argument supplies stagewise interval overlap, package it as
`SinPiIntegral.DyadicNestedRadicalStieltjesCommonWitness.of_overlap`; the
constructor chooses the larger rational lower endpoint as the witness.
Conversely, `DyadicNestedRadicalStieltjesCommonWitness.to_overlap` recovers
the overlap used by stabilization. This changes only the shape of finite
evidence; it does not assert that an exact intermediate real value has been
attained.

For a concrete finite candidate list, use
`SinPiIntegral.canonicalDyadicCertificateSearchAt_some_of_mem_of_admissible`:
an admissible rational witness in the list certifies that the executable
search returns a hit. The remaining all-stage theorem is therefore geometric
witness existence, not search correctness.

The public equal-dyadic transport contract is
`SinPiIntegral.halfIntegral_equiv_of_dyadic_sample_overlap`. It requires the
same fixed plan and one overlap proof for every finite sample. The coordinate
bookkeeping is discharged by
`SinPiIntegral.sinPi_half_dyadic_normalized_sample`, which turns the sample
`2*x` into `k / 2^n`. This is the preferred interface for adding one
nested-radical or other specialized sine evaluator; do not formalize a second
global sine function merely to obtain the integral.

When the geometric proof supplies explicit rational witnesses, package them
with `DyadicTangentWitnessFamily.of_canonical_candidate_family`; it derives the
finite search-hit obligations from list membership and admissibility.

For the squared-sine route, use
`DyadicNestedRadicalSquareTangentCommonWitness.of_overlap` to package the
stagewise candidate/anchor overlap. Its `stabilized_equiv_value` theorem
transports the stabilized candidate to the value represented by the unscaled
quarter-turn chart. The rational value `1/4` is obtained only after the
`reciprocalPiRaw` normalization and its quarter-scale equivalence; the
obsolete unscaled quarter-value contract is explicitly refuted by
`TangentSquareIntegralValueSubgoal.impossible`. The remaining obligation is
therefore the normalized finite overlap family itself, not witness construction
or prefix stabilization. Once the quarter-turn certificate is assembled,
`NormalizedTangentSquareValueSubgoal.of_quarter_turn` performs the product
transport automatically. The provider-facing shortcut
`NormalizedTangentSquareValueSubgoal.of_common_witness` assembles the
quarter-turn certificate from the finite common-witness and endpoint inputs.

The future canonical-logarithm π formula has one explicit entry point:
`PiProofs.CanonicalLogTwoCertificate`. Supply a valid raw value at two and
a proof that it agrees with `Logarithm.logTwoReciprocalIntegral`; then
`PiProofs.piFromCanonicalLogTwo_equiv_piCircleArea` proves the full
integration-by-parts π equivalence. This deliberately does not create a
certificate for the inverse-exponential logarithm—the remaining analytic
work is precisely to construct that input certificate.

For views deliberately outside `PiPresentation`—for example
`pi.integrationByPartsMesh` and `pi.triangleLogSeries`—use
`pi.representations_equiv source target`. It specializes the generic
`Real.Representation.equiv`: two certified views of the same abstract `Real`
have equivalent raw evaluators. This gives supplementary pi computations the
same pairwise API without treating implementation variants as new scorecard
capabilities.

```lean
example : pi.triangleLogSeries.raw.Equiv pi.integrationByPartsMesh.raw :=
  pi.representations_equiv _ _
```
`pi.symmetricCauchy` is the bounded formula assembled over `[-1,0,1]` by the
public piecewise-monotone interface; it checks the increasing and decreasing
branches separately and has direct width bound `16 / (n+1)`.

## Linear systems and Peano--Baker

For a finite sampled model, `LinearODE.DiscreteLinearSystem` is usable now.
It provides a rational-matrix trajectory, recurrence specification and
uniqueness, chronological transition product, and a discrete Duhamel formula.
`LinearODE.peanoBakerDiscreteSum` equals the finite chronological Euler
product.  `LinearODE.peanoBakerFactorialTailShift` turns a nonnegative
rational norm-length bound and requested rational error into an executable
factorial-tail shift.
For a square-zero constant generator, the finite uniform-mesh transition is
already exact: `chronologicalProduct_constant_square_zero_uniform_step` proves
the result is `I + T A` for every positive finite mesh size.  This is a useful
terminating ODE representative before any convergence theorem is invoked.

The finite rotation core exposes two matching exact prefix identities:
`RotationSystem.simplexPartial_even_split` gives
`sum_(r < 2*n) T^r/r! * J^r = C_n(T) * I + S_n(T) * J`, while
`RotationSeries.expPartial_imaginary_even_split` gives
`expPrefix_(2*n)(i*T) = C_n(T) + i*S_n(T)`. The executable rational prefixes
are `cosinePrefix` and `sinePrefix`. `RotationSeries.rotationExpRaw T` now
encloses those even prefixes in valid nested complex boxes, and
`rotationExpRaw_width_le_geometric` bounds both coordinate widths by
`8 * rotationTailMagnitude T 0 * (1/2)^n`. This is a certified complex
series computation at rational `i*T`; `rotationCosRaw` and `rotationSinRaw`
are its valid coordinate raw reals. `RotationCalculus` additionally turns the
shared bounded-input prefix and its `16 * |x-y|` box transport into literal
rational epsilon--delta continuity for each coordinate on `[-2,2]`.
`RotationDerivative.uniformRotationSinOnTwo_hasDerivativeOnInterval` now
adds the full raw interval derivative `sin' = cos` for that same
common-prefix chart, and
`RotationDerivative.uniformRotationCosOnTwo_hasDerivativeOnInterval` adds
`cos' = -sin`. `RotationInitialValues.uniformRotationOnTwo_rotationInitialCertificate`
also packages the literal boxes `C(0)=1`, `S(0)=0` with those derivatives.
On the geometric side,
`GeometricRotationODE.pointOnUnit_geometricRotationSystemCertificate` now
certifies the rational chart on `[0,1]` as
`P' = (2 i / (1+t*t)) P`, with `P(0)=1` and `P(1)=i`, coordinate by
coordinate.  `SectorAreaReparametrization.angleOnUnit_hasDerivative` now
also certifies the represented sector-time coordinate
`Theta(t) = 2 * arctan.rectangle(t)` with
`Theta' = 2/(1+t*t)`, and
`angleAt_equiv_two_arctanGeom` identifies its rational samples with the
geometric angle. It is not yet a summed continuous matrix series, an inverse
sector-area reparametrization of the curve, geometric trigonometry, or Euler
identity.

This is ideal for proving identities about a *given rational discretization*.
It is not yet a theorem that a continuous ODE has a solution represented by a
Peano--Baker interval series.  Keep discretization error and continuous
existence as separate proof obligations.

## Reusing inverse-search plumbing

Do not create a new inverse record for every special function.  A branch with
gap-dependent separation should provide a `GapAwareInverseBisectionPlan`: its
finite midpoint decisions, ordered/nested outputs with a width modulus, and
the forward-image overlap certificate.  The theorem
`GapAwareInverseBisectionPlan.valid_output` derives the full `RealRaw` validity
from those elementary fields.  `gapAwareInverseBisectionPlanToSearch`
converts that plan to the common `GapAwareInverseBisectionSearch` interface,
and `gapAwareInverseBisectionPlan_has_search` assembles a whole branch.
When the output is the standard fixed midpoint iterator, use
`gapAwareInverseBisectionPlanOfFixedIterate` so its dependent interval proofs
are inferred once by the shared constructor.
When evaluator precision must follow a separate schedule, use
`GapAwareScheduledInverseBisectionPlan` and
`gapAwareScheduledInverseBisectionPlan_has_search`; the scheduled adapter
preserves the same explicit `RealRaw.ValidCompute` obligations.
When the precision must inspect the current bracket, use
`gapAwareTargetBisectionAdaptiveIterate` and
`gapAwareTargetBisectionAdaptiveDecision`.  This is the natural interface for
the exponential gap modulus; the exact width theorem remains conditional only
on the supplied finite decision certificates.
If the chosen precision ignores the bracket, the adapter theorem
`gapAwareTargetBisectionAdaptiveIterate_eq_scheduled` identifies this adaptive
run with the scheduled run exactly.  The concrete
`uniformExpOnUnitWarm_oneThird_adaptive_equals_scheduled` theorem records this
connection for the certified `1/3` exponential target.
This leaves function-specific mathematics in the certificate and keeps the
routine `RealRaw`/inverse construction shared.

The squared-sine transport has one executable square-aware witness checkpoint:
`rationalTangentSquareWitnessSearch_stage_one_demo` finds `103/256` at the
first nonzero dyadic sample, and
`dyadicNestedRadicalStage_one_square_complement_overlap` proves the resulting
sine-square / one-minus-cosine-square overlap.  This is deliberately one
representative finite cell; the remaining work is the uniform witness family,
not a repetition of the same calculation for every cell.
The reusable bridge is
`square_overlap_of_rationalTangentSquareWitnessSearch`: once a search result
and the two unit-interval box bounds are available, it supplies the circle
identity and square/complement overlap automatically.
Its signed counterpart,
`signed_square_overlap_of_rationalTangentSquareWitnessSearch`, accepts the
natural cosine range `[-1,1]` and uses the signed square enclosure below.
Its family-level form,
`dyadicNestedRadicalStage_square_complement_overlap_of_search_family`, reduces
the transport to a uniform search-success theorem plus the automatically
proved cosine-box bound `dyadicNestedRadicalStageCosAt_subinterval`;
the sine-box bound is now discharged uniformly by
`dyadicNestedRadicalStageSinAt_subinterval`.  The cosine condition is kept
explicit because the full half-interval includes negative cosine values, so a
nonnegative-only square interval must not be applied there silently.
The signed enclosure handles that crossing directly:
`rationalSquareIntervalSigned` and `rationalOneMinusSquareIntervalSigned`
split at zero, while `rationalSquareIntervalSigned_contains` and
`rationalSquareInterval_overlap_oneMinusSquareInterval_of_circle_signed`
provide the reusable proof bridge.  This is one signed representative, not a
new theorem family for every sign pattern.

## Completion and trust checklist

Before presenting a result as established, check all of the following:

- the theorem is a proof, not just a `def`, `structure`, `Prop`, or
  `Nonempty` target;
- every raw value used in the conclusion has a validity certificate;
- all domain and endpoint hypotheses are carried through;
- formal series identities have not been promoted to analytic raw-function
  claims without convergence and derivative certificates;
- a definite-integral formula includes an integral construction and endpoint
  bridge, not merely a derivative calculation;
- the relevant module builds with `lake build`; and
- `rg -n 'sorry|admit|axiom' <files-used>` has been reviewed.  This is a
  source audit, not a substitute for understanding Lean's trusted kernel and
  imported axioms.

When the boundary is unclear, report it plainly in the proof statement and
add the missing bridge to [GOALS.md](GOALS.md), rather than silently importing
classical real analysis.  That discipline is what makes the project useful as
a checkable foundation instead of a collection of familiar-looking formulas.
