# Formalization Guide for Humans and LLMs

This is the short entry point for using this repository as a constructive,
rational-certificate foundation.  It is for a reader who wants to formalize a
new theorem from science, engineering, or first-year calculus without first
reading the entire Pi project.

The central rule is simple: state a computation as an algorithm returning
rational intervals, prove that its boxes are valid and shrink, and connect it
to the desired theorem through explicit finite certificates.  Do not replace a
missing certificate with an appeal to completed real numbers, topology, or a
Mathlib analysis theorem.

For an external human or agent that needs a repeatable procedure rather than
just an API map, start with the public
[computable-analysis formalization skill](skills/computable-analysis-formalization/SKILL.md).
Its integral reference documents the per-function constructions, including a
shrinking rational bracket around a non-rational turning point.

## Read this first

The repository is deliberately not a drop-in replacement for Mathlib.  Its
current strong point is checking narrowly specified rational one-variable
arguments and finite linear-system arguments.  It is not yet capable of
formalizing arbitrary scientific models end to end.  In particular, the
following are still open as *general* theorems:

- product, chain, and quotient rules for arbitrary interval evaluators;
- construction of an integral from every interval-regular function;
- general FTC, substitution, and bounded piecewise integration-by-parts;
- analytic certificates for the selected `exp`, `log`, `sin`, and `cos` raw
  functions, including `exp' = exp`;
- continuous matrix Peano--Baker and constructive linear
  Picard--Lindelöf; and
- numerical-error, PDE, units, and broad complex-domain infrastructure.

A declaration may be a useful interface, a target `Prop`, or a fully proved
theorem.  The guide calls out that distinction.  A named `def` or `structure`
is never evidence that its intended mathematical theorem has been proved.

## Foundation boundary and reproducible audit

The project source deliberately has no imports from `Mathlib`, `Std`, or
`Batteries`.  The only foundation import is
`Init.Grind.Ordered.Rat` in `ComputableAnalysis.Basic`; every other source
import is another `ComputableAnalysis` module.  The manifest's only external
package is `checkdecls`, which validates the blueprint's declaration links.
Thus the project is not silently using a completed-real analysis library; it
uses Lean's rational arithmetic and its own interval constructions.

This is an import boundary, not a mathematical theorem.  It does not by
itself show that a proposed declaration avoids a completeness-like assumption:
read the declaration and its certificate hypotheses.  Before depending on a
new module or publishing a material update, rerun this compact audit from the
repository root:

```bash
rg -n '^import\s+(Mathlib|Mathlib\.|Std\.|Batteries\.)' ComputableAnalysis
rg -n '\b(sorry|admit)\b' ComputableAnalysis
lake build ComputableAnalysis
lake env .lake/packages/checkdecls/.lake/build/bin/checkdecls blueprint/lean_decls
```

The first two commands should print nothing.  The build and declaration check
then establish that the project modules and every Lean name cited in the
blueprint compile in the selected Lean toolchain.  This audit is intentionally
simple enough for an LLM or a contributor to repeat before treating the
repository as a dependency.

## Fast navigation

Start with the smallest target module rather than importing
`ComputableAnalysis` (the root module imports the whole experiment).

| Need | Import | Start with |
| --- | --- | --- |
| Rational interval arithmetic and raw reals | `ComputableAnalysis.Basic` | `QInterval`, `RealRaw`, `RealRaw.Valid`, `RealRaw.Equiv` |
| Rational function with a certified domain | `ComputableAnalysis.FunctionDomains` | `RatFun`, `RatFun.DenominatorApartOnInterval`, `RatFun.onRegularInterval` |
| Interval functions, continuity, and integral certificates | `ComputableAnalysis.Calculus` | `FunctionOnInterval`, `IntervalRegularOn`, `Integral.nondecreasingDarbouxDyadicStage`, `Integral.ConstructionFor` |
| One non-rational turning point in an integral | `ComputableAnalysis.TurningPointIntegral` | `Integral.TurningPointBracket`, `Integral.SingleTurnIntegralCandidate` |
| Rational finite-difference derivatives | `ComputableAnalysis.Differential` | `HasDerivativeOnInterval`, `HasForwardDerivativeAt` |
| Definite-integral-to-endpoint packages and concrete arctangent work | `ComputableAnalysis.IntegralIdentities` | `Integral.DefiniteIdentityFor`, `IntegralIdentities` |
| Formal power series and rational tail bounds | `ComputableAnalysis.PowerSeries` | `FormalPowerSeries`, `RationalMajorant` |
| Current first-year derivative ledger | `ComputableAnalysis.FirstYearCalculus` | `checked_power_series_table`, `RealElementary` |
| Positive powers, exponential/log interfaces | `ComputableAnalysis.ElementaryFunctions` | `exp.PositiveRealRaw`, `exp.RationalPowerExtension`, `exp.ExponentialFunction` |
| Discrete linear ODE / Peano--Baker core | `ComputableAnalysis.PeanoBaker` | `LinearODE.DiscreteLinearSystem`, `chronologicalProduct`, `peanoBakerDiscreteSum` |
| Certified complex rotation series | `ComputableAnalysis.RotationSeries` | `rotationExpRaw`, `rotationCosRaw`, `rotationSinRaw`, and their validity/rate theorems |
| Algebraic branches and square roots | `ComputableAnalysis.AlgebraicFunctions` | source header and the unit-interval square-root examples |
| Complex interval polynomial checks | `ComputableAnalysis.ComplexInterval` | `QBox.evalPoly`, `IsApproxRootAt` |

For the mathematical status and intended dependency order, use
[GOALS.md](GOALS.md).  For a readable, declaration-linked account, use the
[blueprint](blueprint/README.md).  The derivative table is in
[`blueprint/src/04-infinite-series.tex`](blueprint/src/04-infinite-series.tex),
not in this guide.

### Module atlas

Use this as a routing index, not as a claim that every module exposes a
finished general theorem.

| Family | Modules | Use them for |
| --- | --- | --- |
| Foundation | `Basic`, `Algebraic`, `AlgebraicNumbers`, `AlgebraicFunctions`, `FunctionDomains`, `Extension`, `Calculus`, `Differential`, `MonotonicityConvexity`, `FTC` | Raw interval representations, domains, continuity, inverse branches, finite derivatives, integral/FTC certificate interfaces |
| Elementary functions and series | `Elementary`, `ElementaryFunctions`, `Exp`, `ExpProofs`, `Logarithm`, `PowerSeries`, `Series`, `Taylor`, `FirstYearCalculus` | Power-series algorithms, rational majorants, exp/log comparison interfaces, and the current formal derivative ledger |
| Integrals and special computations | `TurningPointIntegral`, `IntegralIdentities`, `ArctanGeometry`, `ArctanPresentations`, `AbelianIntegrals`, `ComplexPathIntegral`, `DirichletSeries`, `Basel`, `FTA` | Concrete interval constructions and theorems/targets connecting them to geometric or series algorithms |
| Geometry, Pi, and ODEs | `RationalCircle`, `TrigSpecialValues`, `GaussSeventeen`, `Pi`, `PiProofs`, `Nilakantha`, `PeanoBaker`, `RotationSeries` | Rational-circle geometry, explicitly status-marked special values, Pi coverage tests, finite ODE algebra, and the certified imaginary-axis complex series |
| Polynomial and complex checks | `Polynomial`, `ComplexPolynomial`, `ComplexInterval` | Exact polynomial algebra and rational complex-box root checks |

`Playground`, `MembershipCheck`, and the repair/check files are development
support rather than a stable downstream API.  Prefer a theorem in one of the
families above, and consult its module header before using it.

## Five representations to keep separate

Most mistakes come from conflating these layers.

| Object | Meaning | What it does not provide automatically |
| --- | --- | --- |
| `QInterval` | A rational enclosure `[lo, hi]` | A real number or a shrinking proof |
| `RealRaw` | A sequence of rational interval boxes | Validity; supply `RealRaw.Valid` |
| `RealRaw.Equiv` | Overlap-based equality of two valid raw reals | Equality of implementations by definitional reduction |
| `PartialRealFunRaw` | A function with a pointwise domain | A whole-interval domain certificate |
| `FunctionOnInterval` | A partial function certified at every rational point of `[a,b]` | Continuity, interval regularity, differentiability, or integrability |

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

`FirstYearCalculus.checked_power_series_table` proves the coefficient-level
identities for exp, sin, cos, sinh, and cosh.  Those formal identities are not
yet interval-analytic derivative theorems for the corresponding boxed raw
functions.  This distinction must be preserved in downstream proofs.

The first exponential finite-difference brick is also available:
`expTaylorQuadratic x = 1 + x + x^2/2`, and
`ExpProofs.expTaylorQuadratic_forwardDerivativeAtZero` proves a
`HasForwardDerivativeAt` certificate at zero with derivative `1`.
Its literal quotient is `1 + h/2`.  The actual tail-enclosed evaluator has
now crossed the same local gate:
`ExpProofs.expPowerSeriesOnUnit_forwardDerivativeAtZero` proves its forward
derivative at zero is `1`.  Its proof uses the literal public stage-zero
finite sum, whose positive tail and geometric radius are both bounded by
`h^2` on positive half-unit steps.  This is not a global `exp' = exp`
certificate on an interval.

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

`FTC.EffectiveFTC` and `FTC.effectiveFTC_definiteIntegralEqualsEndpoint`
describe one checked endpoint-bridge route.  The generic bridge from an
arbitrary `HasDerivativeOnInterval` to that FTC certificate is not yet
available.  The finite integration-by-parts construction in
`IntegralIdentities.lean` is a benchmark and a source of reusable finite
algebra, not a universal theorem.  Consequently, an LLM must currently
either stay within an existing concrete construction or make the missing
general theorem its explicit proof goal.

### Increasing pieces: start with the literal finite stage

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

### A single non-rational turning point

When an integrand is certified increasing up to a turning point and decreasing
after it, do not pretend that the turn has a rational coordinate.  Use
`Integral.TurningPointBracket`: its raw interval boxes supply rational
endpoints `[ell_n, r_n]` that shrink around the unknown turn.  At stage `n`,
construct the two outer integrals on `[a, ell_n]` and `[r_n, b]`.  Enclose the
unresolved middle values in one fixed rational range `B`; the literal middle
box is `(r_n - ell_n) * B`.  `Integral.SingleTurnIntegralCandidate` proves
that this middle width, and then the width of the three-part sum, tends to
zero.  Its `middleBox_contained_symmetric` theorem supplies the sharper
vanishing bound from any absolute-value enclosure.

This is deliberately a per-function workflow.  `SingleTurnIntegralCompletion`
is the remaining proof obligation that the three boxes enclose that
function's intended integral representative.  It does not turn every bounded
or continuous interval function into an integral.

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

These are mostly interfaces and comparison targets.  Do not claim that the
repository has proved a general rational-power construction, `exp' = exp`, or
the full exp/log equivalence.  The next analytic milestone is an actual boxed
exponential with a `HasDerivativeOnInterval` self-derivative certificate,
then uniqueness from the Peano--Baker route.

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
power-series evaluator has forward derivative `1` at zero.  It is deliberately
kept distinct from the still-open interval self-derivative certificate needed
by `SolvesSelfDerivativeOnInterval`.

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
#check ExpProofs.expPowerSeries_zero_compute_eq
#check ExpProofs.expPowerSeries_zero_valid
#check ExpProofs.expPowerSeries_zero_equiv_one
#check expTaylorQuadratic
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
agreement, the checked local forward derivative at zero, and the still-open
global derivative/ODE certificate distinct.

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
```

These names expose the certified complex series at rational imaginary inputs;
their real and imaginary coordinates are certified rational-input power-series
computations, not yet geometric trigonometry.

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
```

This is why the special-values table colors only its arctangent-witness
column: the displayed sine and cosine entries follow by rational algebra once
that one equation is certified. At present, only the two endpoint witness
equations are fully proved; the non-endpoint rows remain computation-ready
targets until their raw-slope equalities are formalized.

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
pretending that the comparison adds a new calculus capability.  `pi.integrationByParts` is the checked supplied-unit
formula using the literal reciprocal-integral logarithm, with runtime bound
`52 / 2^n`; it is a finite calculus bridge, not the still-open general
integration-by-parts theorem or canonical-exp/log transport.
`pi.squareSubstitution` is a separate checked bridge with runtime bound
`56 / 2^n`: its raw formula retains the pullback integral
`2 * ∫_0^1 2*x/(1+x*x) dx`, and its agreement with
`pi.integrationByParts` is the finite `t = x*x` substitution certificate.
It is likewise not a general substitution theorem.
`pi.squareStieltjes` is the supplementary direct-mesh view: it evaluates
the stabilized finite Stieltjes sums for the same substitution, then proves
equivalent to `pi.squareSubstitution` and area pi.  It is an executable
algorithmic witness in the primary pi registry, not a ninth coverage bridge.

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
are its valid coordinate raw reals. It is not yet a summed continuous matrix
series, geometric trigonometry, or Euler identity.

This is ideal for proving identities about a *given rational discretization*.
It is not yet a theorem that a continuous ODE has a solution represented by a
Peano--Baker interval series.  Keep discretization error and continuous
existence as separate proof obligations.

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
