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
| Interval functions, continuity, and integral certificates | `ComputableAnalysis.Calculus` | `FunctionOnInterval`, `IntervalRegularOn`, `Integral.ConstructionFor` |
| One non-rational turning point in an integral | `ComputableAnalysis.TurningPointIntegral` | `Integral.TurningPointBracket`, `Integral.SingleTurnIntegralCandidate` |
| Rational finite-difference derivatives | `ComputableAnalysis.Differential` | `HasDerivativeOnInterval`, `HasForwardDerivativeAt` |
| Definite-integral-to-endpoint packages and concrete arctangent work | `ComputableAnalysis.IntegralIdentities` | `Integral.DefiniteIdentityFor`, `IntegralIdentities` |
| Formal power series and rational tail bounds | `ComputableAnalysis.PowerSeries` | `FormalPowerSeries`, `RationalMajorant` |
| Current first-year derivative ledger | `ComputableAnalysis.FirstYearCalculus` | `checked_power_series_table`, `RealElementary` |
| Positive powers, exponential/log interfaces | `ComputableAnalysis.ElementaryFunctions` | `exp.PositiveRealRaw`, `exp.RationalPowerExtension`, `exp.ExponentialFunction` |
| Discrete linear ODE / Peano--Baker core | `ComputableAnalysis.PeanoBaker` | `LinearODE.DiscreteLinearSystem`, `chronologicalProduct`, `peanoBakerDiscreteSum` |
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
| Geometry, Pi, and ODEs | `RationalCircle`, `TrigSpecialValues`, `GaussSeventeen`, `Pi`, `PiProofs`, `Nilakantha`, `PeanoBaker` | Rational-circle geometry, explicitly status-marked special values, Pi coverage tests, and finite linear-system algebra |
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
#check ExpProofs.expPowerSeries_zero_compute_eq
#check ExpProofs.expPowerSeries_zero_valid
#check ExpProofs.expPowerSeries_zero_equiv_one
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
representations of the same abstract value `e`; it does not establish an
analytic derivative theorem. Keep constant-level agreement distinct from a
derivative/ODE certificate for an exponential function.

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

For rational-circle chord refinements, use
`RationalCircle.Stage.secantChordLower` rather than selecting a square root.
For a nondegenerate positively oriented chord it supplies
`cross + (1 - dot)^2 / (2 * cross + 1 - dot)` and its squared lower-bound
theorem. This is the stronger rational certificate for the remaining direct
circumference diagnostic; it is not a new Pi-registry presentation.
`PiProofs.adjacentSecantChordLower_sub_width_le_segment_lo` connects that
certificate to the concrete lower endpoint used by the original finite
square-root bisection.  A proposed direct-refinement inequality should subtract
the two displayed fine-chord widths from the two secant certificates, then
prove the resulting nonnegative rational is at least the coarse chord in the
squared sense.  This exact target is
`PiProofs.AdjacentChordSecantMarginCoversFineWidths`; its proved reduction
theorem is `PiProofs.adjacentChordLowerRefinesByDoubling_of_secantMargin`.

## Pi as a regression suite, not a target namespace

`PiProofs.PiCoverageBridge` is deliberately a compact list of distinct
end-to-end capability tests.  It currently has eight checked bridges; it is
not a percentage or a catalogue of all certified pi computations.  Consume a
named presentation from the abstract `pi : Real` handle when you need a
specific implementation:

```lean
import ComputableAnalysis.PiProofs

open ComputableAnalysis

#check pi.circleArea
#check pi.circumference
#check pi.arctanGeom
#check pi.integrationByParts
#check pi.squareSubstitution
#check pi.leibniz
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
Leibniz bridge.  Similarly, the direct geometric diagnostic
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

For views deliberately outside `PiPresentation`—for example
`pi.curvatureFan`, `pi.integrationByPartsMesh`, and `pi.triangleLogSeries`—use
`pi.representations_equiv source target`. It specializes the generic
`Real.Representation.equiv`: two certified views of the same abstract `Real`
have equivalent raw evaluators. This gives supplementary pi computations the
same pairwise API without treating implementation variants as new scorecard
capabilities.

```lean
example : pi.triangleLogSeries.raw.Equiv pi.curvatureFan.raw :=
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

The finite constant-coefficient layer also contains the exact rotation-series
coefficient calculation. `LinearODE.RotationSystem.generator` is the rational
matrix `[[0, -1], [1, 0]]`; `generator_square`, `generator_pow_even`, and
`generator_pow_odd` prove its alternating even/odd powers. The corresponding
`simplexTerm_even` and `simplexTerm_odd` normalize every finite
constant Peano--Baker term to its cosine-type or sine-type coefficient. This
is useful when formalizing a future Euler comparison, but it is not a claim
that a continuous matrix series has already been summed.

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
