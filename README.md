# Computable Analysis

The organizing principle is **construct the objects; prove their laws**.
General theorems can start from supplied constructions with proved validity
and mathematical properties. A useful conditional law need not wait for a
universal existence theorem or the weakest possible sufficient conditions.
Concrete examples still require their constructions, and no hypothesis may
silently assume the conclusion. Methods live in the formalization skill;
finite algorithms and their proofs live in Lean. See the
[project-wide contract audit](docs/CONSTRUCTION_FIRST_AUDIT.md).

Proof-oriented calculus from explicit rational interval algorithms.

This project develops real and complex function theory without importing a
completed real-number or measure-theory foundation. Abstract point-set topology
is permitted only within the audited import boundary. A quantity is
computed by finite rational boxes; Lean proves that the boxes are coherent,
shrink to arbitrary precision, and agree with alternative computations.

The guiding route is:

```text
rational intervals
→ circle and trigonometry
→ finite integrals
→ effective FTC
→ power series and Fourier analysis
→ exponential and logarithm
→ linear ODEs
```

## Public API

```lean
import ComputableAnalysis
```

The root exports the canonical calculus foundation, the parallel algebraic
root-certificate foundation, and the scoped Wiedijk challenge registry.
Fixed-stage demonstrations and routine `Finite*Example` modules remain
individually importable but are not part of the public root.

For narrower imports:

- `ComputableAnalysis.Basic`
- `ComputableAnalysis.CircleFoundation`
- `ComputableAnalysis.IntegralFoundation`
- `ComputableAnalysis.EffectiveCalculusFoundation`
- `ComputableAnalysis.SeriesFoundation`
- `ComputableAnalysis.ExponentialLogarithmFoundation`
- `ComputableAnalysis.DifferentialEquationsFoundation`
- `ComputableAnalysis.AlgebraicFoundation`
- `ComputableAnalysis.CalculusFoundation`

These foundation modules collect imports without renaming their declarations;
the canonical theorem name remains the one defined in its subject module.

## Core representation

- `RealRaw` is one stage-indexed rational interval algorithm.
- `Real` retains alternative `RealRaw` implementations and a maintained tree
  of equivalence proofs.
- `FunctionRaw` is one computation on its natural represented domain.
- abstract complex functions retain equivalent computations on intersections
  of their domains.

`ContinuousFunctionOnInterval.applyReal` is the canonical real-input
application operator. Its raw implementation searches for enough input
precision and performs finite prefix stabilization; callers do not supply a
convergence rate. `applyReal_equiv` and `mapImplementation` transport the
result across the maintained implementation tree.

A raw evaluator does not know its equivalence proofs. Adding a new
implementation requires one edge to the existing equivalence tree, not a
quadratic family of pairwise proofs.

## Calculus status

The checked foundation includes finite Darboux and Stieltjes sums, finitely
piecewise monotone integration, rational derivative certificates, explicit
power-series tails, representative Fourier machinery, and finite
Peano--Baker/Duhamel algebra.

The canonical FTC output is
`EffectiveDerivativeBoundFTC.stabilizedBoundedIntegralRaw`: finite derivative
bounds prove that the integral boxes shrink and overlap a valid primitive
endpoint computation; prefix stabilization then supplies nestedness. It does
not assume a completed real line or that independently selected finite sums
were already nested.

`Integral.enclosureRealizationOfEffectiveFTC` can package the whole-cell
ranges and their proved endpoint comparison for the specified derivative.
The older `Integral.effectiveFTCConstructionFor` exposes a numerical candidate,
not the range evidence by itself. These are optional proof packages for a
particular FTC argument. The arctangent kernel \(1/(1+x^2)\) is a checked
non-polynomial client of this route.

The main active application is the equal-dyadic computation of `sin(pi*x)` on
`[0,1/2]`. Its direct nested-radical half-angle tangent is now a valid
`RealRaw`; the remaining geometric theorem is one equivalence edge to the
inverse-arctangent implementation. The larger squared-sine checkpoint and
search portfolios are opt-in modules rather than part of the canonical root.

## Project documents

- [Blueprint](https://liuyao12.github.io/computable-analysis/): algorithms,
  theorem statements, and dependency story.
- [GOALS.md](GOALS.md): concise canonical roadmap and current frontier.
- [FORMALIZATION_GUIDE.md](FORMALIZATION_GUIDE.md): contributor/agent workflow.
- [COMPARISON.md](COMPARISON.md): comparison with other formalizations.
- [Formalization skill](skills/computable-analysis-formalization/SKILL.md):
  reusable procedural guide.

The preface contains two navigation scoreboards: independent computations of
pi, and the 16 analysis-relevant entries selected from
[Freek Wiedijk's list of 100 theorems](https://www.cs.ru.nl/~freek/100/).
Neither is a percentage-complete measure of calculus.

## Build

The project targets Lean 4.33.

```sh
lake build ComputableAnalysis.CalculusFoundation ComputableAnalysis
```

The source depends on Lean's rational ordered-arithmetic substrate and project
modules. The canonical chain does not import mathlib's standard real numbers.

## Contribution rule

Add a theorem when it contributes a new evaluator, domain, quantitative
estimate, convergence certificate, or representation edge. Reuse finite
algebra and combinatorics. Keep one representative of a routine family, and
derive scalar, sign, degree, and finite-piece variants by transport.

## Fuchs–Painlevé subproject

Import `ComputableAnalysis.AlgebraicODE` for polynomial differential residuals,
Euler–Fuchs coefficient classification, formal nonresonant Frobenius solutions,
all-degree terminating Laguerre polynomials with both derivative certificates,
and Painlevé II algebraic seeds. The
[subproject ledger and comparison research](docs/FUCHS_PAINLEVE.md) separates
checked results from the open general classification. No Mathlib reals are used.
