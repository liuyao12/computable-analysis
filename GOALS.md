# Computable Analysis: Canonical Roadmap

## Aim

Build a usable foundation for calculus and elementary function theory from
explicit rational computations, without importing a completed real-number,
topological, or measure-theoretic foundation.

A theorem is in scope when its infinite process is represented by finite data
at every stage and the Lean proof supplies the quantitative certificate that
makes those stages coherent. Routine finite algebra and combinatorics should
be reused from Lean rather than duplicated here.

## Canonical objects

- `RealRaw`: one stage-indexed rational-interval computation.
- `Real`: one or more `RealRaw` implementations connected by enough
  equivalence edges to form a maintained spanning tree.
- `FunctionRaw`: one computation on its natural represented domain.
- `ComplexFunction`: equivalent function computations, compared only where
  their domains overlap.

`RealRaw` and `FunctionRaw` do not store equivalence proofs. The abstract
objects do. A new implementation needs one edge to an existing implementation,
not pairwise proofs against every implementation.

## Canonical imports

New clients should import `ComputableAnalysis` or one of these narrower entry
points:

| Area | Module |
| --- | --- |
| raw and abstract represented numbers | `ComputableAnalysis.Basic` |
| rational circle and trigonometry | `ComputableAnalysis.CircleFoundation` |
| finite integrals and endpoint identities | `ComputableAnalysis.IntegralFoundation` |
| effective derivatives, MVT, and FTC | `ComputableAnalysis.EffectiveCalculusFoundation` |
| power series and Fourier certificates | `ComputableAnalysis.SeriesFoundation` |
| exponential and logarithm | `ComputableAnalysis.ExponentialLogarithmFoundation` |
| linear ODEs | `ComputableAnalysis.DifferentialEquationsFoundation` |
| algebraic numbers and finite root certificates | `ComputableAnalysis.AlgebraicFoundation` |
| complete calculus route | `ComputableAnalysis.CalculusFoundation` |

Worked `Finite*Example` modules are regression tests and examples. They are
not re-exported by the canonical root.

## Checked foundation

### Represented numbers

- Rational interval algorithms, nestedness, shrinking widths, arithmetic,
  order, and overlap equivalence are checked.
- Prefix stabilization turns shrinking, non-nested candidate intervals into a
  valid `RealRaw` when they overlap a valid anchor.
- `RealRaw.overlapChainStabilize` composes two overlap edges even when the
  middle candidate is not valid. It widens by the middle width before prefix
  stabilization; it does not falsely treat interval overlap as transitive.
- Rational square roots and the project-native irrationality theorem are
  checked without standard real numbers.

### Circle and trigonometry

- Rational parametrization of the circle, rational area bounds, arctangent
  presentations, nested-radical dyadic sine values, and finite complex
  rotations are executable.
- Independent pi computations are connected by explicit `RealRaw.Equiv`
  theorems.

### Integration and FTC

- Monotone Darboux rectangles, finitely piecewise monotone assembly, finite
  Stieltjes sums, polynomial examples, and the arctangent example are checked.
- `EffectiveDerivativeBoundFTC.stabilizedBoundedIntegralRaw_valid` is the
  canonical FTC closure. It derives validity from the derivative certificate,
  shrinking finite-sum widths, and a valid endpoint computation. It does not
  assume that the native Riemann candidate was already nested.
- The matching equivalence theorem identifies the stabilized integral with
  the primitive's endpoint difference.
- `FunctionOnInterval.ofRealFunRaw` records a certified raw integrand on its
  rational interval, and `Integral.effectiveFTCConstructionFor` turns the
  stabilized FTC output directly into the domain-aware integral API.
- The arctangent kernel is the canonical non-polynomial client: it supplies
  one `EffectiveDerivativeBoundFTC` certificate and obtains its construction,
  validity, and endpoint identity from the general route without local
  stabilization wrappers.
- The nonlinear regression `(x - x^3/6)^2` on `[0,1/2]` now uses this
  construction route and is identified with `6389/161280`.

### Series, special functions, and ODEs

- Finite power-series algebra, explicit tails, finite Taylor FTC, finite
  Fourier transforms, and representative effective Fourier tails are checked.
- Exponential and logarithm have explicit rational evaluators and substantial
  derivative, inverse, and representation bridges.
- Finite Peano--Baker products, discrete Duhamel sums, and factorial-tail
  estimates provide the linear-ODE core.

## Active frontier

Work in dependency order. Do not add routine examples while an earlier bridge
is open.

1. **Equal-dyadic sine transport.** Construct the uniform finite geometric
   certificate connecting nested-radical dyadic samples to the rational-circle
   or tangent representation.
2. **Squared sine.** Supply the two substantive pairwise certificates:
   public dyadic squares overlap the nested-radical computation, and the
   nested-radical computation overlaps the normalized tangent-square anchor.
   The canonical chain stabilizer then gives a valid integral equivalent to
   `1/4`; a stronger three-way same-stage witness is unnecessary.
3. **Fourier series.** Complete effective reconstruction for one genuinely
   infinite, nontrivial class with explicit coefficient and tail schedules.
4. **Linear ODEs.** Lift finite Peano--Baker/Duhamel algebra to interval-valued
   simplex computations with a uniform factorial-tail certificate, then prove
   uniqueness.
5. **Complex special functions.** Treat special functions as complex-variable
   computations from the start, adding one representative per new evaluator
   or analytic estimate.

## Effective FTC contract

For a primitive computation `F`, derivative computation `dF`, and rational
endpoints `a ≤ b`, a provider supplies:

1. domains for `F` and `dF`;
2. finite rational partitions;
3. derivative boxes on each cell;
4. containment of each scaled derivative box around the endpoint increment;
5. a rational width budget tending to zero;
6. a valid endpoint-difference computation.

The library forms finite bounded sums, proves their widths shrink, stabilizes
them against the endpoint computation, and returns an
`Integral.ConstructionFor` whose integral is equivalent to `F(b) - F(a)`. No
theorem that every continuous function is integrable is needed for this
workflow.

## Wiedijk challenge

The project tracks only the 16 entries from Freek Wiedijk's list whose content
is genuinely relevant to represented numbers, infinite processes, calculus,
or function theory. The machine-readable list is
`ComputableAnalysis.wiedijkAnalysisEntries`; the preface
links each item to its blueprint statement.

Finite arithmetic, counting, elementary coordinate geometry, and similar
items are excluded even when a short Lean proof exists. They can be imported
from Lean when an analytic proof needs them.

## Canonization rule

- One canonical declaration owns each concept.
- Subject modules contain proofs; scoreboard and foundation modules index or
  import them rather than reproving them under new names.
- Keep one representative for a computational pattern. Derive scalar,
  sign, degree, and finite-piece variants by transport.
- Mark compatibility adapters as legacy and do not link them from the
  blueprint.
- A provider structure is not counted as a completed theorem until an
  inhabitant and its endpoint/value theorem are checked.
- No `sorry`, `admit`, standard real numbers, measure theory, or hidden
  completeness enters the canonical import chain.

## Release checks

Before publishing:

1. build `ComputableAnalysis.CalculusFoundation` and `ComputableAnalysis`;
2. run the blueprint declaration checker;
3. render the blueprint web output;
4. inspect changed files for `sorry`/`admit` and stale legacy links;
5. commit, push to `main`, and confirm both Lean CI and GitHub Pages.
