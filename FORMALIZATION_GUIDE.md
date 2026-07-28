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

## Fast navigation

Start with the smallest target module rather than importing
`ComputableAnalysis` (the root module imports the whole experiment).

| Need | Import | Start with |
| --- | --- | --- |
| Rational interval arithmetic and raw reals | `ComputableAnalysis.Basic` | `QInterval`, `RealRaw`, `RealRaw.Valid`, `RealRaw.Equiv` |
| Rational function with a certified domain | `ComputableAnalysis.FunctionDomains` | `RatFun`, `RatFun.DenominatorApartOnInterval`, `RatFun.onRegularInterval` |
| Interval functions, continuity, and integral certificates | `ComputableAnalysis.Calculus` | `FunctionOnInterval`, `IntervalRegularOn`, `Integral.ConstructionFor` |
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
| Integrals and special computations | `IntegralIdentities`, `ArctanGeometry`, `ArctanPresentations`, `AbelianIntegrals`, `ComplexPathIntegral`, `DirichletSeries`, `Basel`, `FTA` | Concrete interval constructions and theorems/targets connecting them to geometric or series algorithms |
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

The rational-circle and arctangent code contains useful geometric and
power-series computations, but normalized-angle sine/cosine/tangent special
values remain partly target-level.  Consult the green/orange legend in the
blueprint before relying on one.

## Linear systems and Peano--Baker

For a finite sampled model, `LinearODE.DiscreteLinearSystem` is usable now.
It provides a rational-matrix trajectory, recurrence specification and
uniqueness, chronological transition product, and a discrete Duhamel formula.
`LinearODE.peanoBakerDiscreteSum` equals the finite chronological Euler
product.  `LinearODE.peanoBakerFactorialTailShift` turns a nonnegative
rational norm-length bound and requested rational error into an executable
factorial-tail shift.

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
