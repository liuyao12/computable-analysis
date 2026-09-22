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
| particular tagged-quadrature certificates | `ComputableAnalysis.QuadratureAdapters` |
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
- The oriented dyadic cosine table has one canonical nonnegative-magnitude
  projection. Together with the sine boxes it gives a half-angle tangent
  `RealRaw` whose stabilized form is valid without a completed-real anchor.
- The regular arctangent branch reuses the accelerated sector-area clock by
  one-half scaling; it has interval regularity, monotonicity, and effective
  inverse separation without a second schedule.
- Effective inverse branches have a generic source-uniqueness theorem based
  on equivalent forward interval computations and finite separation.
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

## Active frontier: finish the elementary infrastructure

The current priority is ordinary, finite-valued single-variable calculus.
Develop reusable constructors and rules; use routine calculations as disposable
tests against a fixed library. Preserve the geometric circle/trigonometric
computations and the specially selected mathematical comparisons.

1. **Integral meaning and assembly.** The new quantitative tagged-dyadic
   certificate preserves the relation between a supplied integrand and a valid
   number computation. Monotone-sample and rational-Lipschitz adapters are
   implemented. Finish the effective-FTC adapter, oriented interval transports,
   splitting, and change-of-variable comparisons before general migration.
   Legacy numerical validity alone is not an integral certificate.
2. **Local calculus and Taylor.** Reuse `TaylorFTC` from the elementary-calculus
   branch; do not restart its arbitrary-order weighted-FTC proof. Complete
   arbitrary rational-chart transport and composable derivative certificates,
   including computed-input composition and the required error allocation.
3. **Elementary functions.** Consolidate bounded exponential, positive-interval
   logarithm, their inverse identities, and full geometric trigonometry with
   correct normalization and agreement at chart joins. Close concrete provider
   instances rather than introducing another family of obligations.
4. **Certified equations and optimization.** Build reusable refinement,
   uniqueness and error-estimation rules from the completed calculus. Specific
   objectives or elementary integral evaluations are acceptance tests, not
   automatic new library modules.
5. **Independent comparison and release.** Prove the same complete native
   propositions in the optional Mathlib workspace, with all representation
   bridges and hypotheses explicit. Repair the known broad `PiProofs` build
   failure before claiming a full release; focused verification is separate.

### Existing inverse work must be reused

`ClosedArctanInverse.search` and `provider` supply a concrete normalized
arctangent inverse with validity, domain containment and forward equivalence.
The previous roadmap's request to construct this canonical instance is obsolete.
That does not automatically discharge every older gap-aware or dyadic-table
provider: identify the exact declaration and hypotheses before migrating one.
The dyadic radical representation and squared-sine transport obligations in the
formalization guide must not be relabeled complete merely from the inverse's
existence, nor should they trigger another duplicate inverse algorithm.

Fourier reconstruction, general linear ODE solution constructors, Gamma,
Stirling, singular functions and PDEs remain independent subsequent directions.
Their interface records and finite algebra are not advertised as complete
analytic solutions, and they are not prerequisites for finishing this core.

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
- Keep a compatibility adapter only while a concrete consumer needs it;
  otherwise remove the closed adapter chain. Do not link adapters from the
  blueprint.
- A provider structure is not counted as a completed theorem until an
  inhabitant and its endpoint/value theorem are checked.
- Do not keep orphan portfolio, checkpoint, or assumption-repackaging modules
  in the source tree.  Git history is the archive for superseded proof routes.
- No `sorry`, `admit`, standard real numbers, measure theory, or hidden
  completeness enters the canonical import chain.

## Release checks

Before publishing:

1. build `ComputableAnalysis.CalculusFoundation`, `ComputableAnalysis`, and
   `ComputableAnalysis.PiProofs` (the canonical arctangent/\(\pi\) bridge);
2. run the blueprint declaration checker;
3. render the blueprint web output;
4. inspect changed files for `sorry`/`admit` and stale legacy links;
5. commit, push to `main`, and confirm both Lean CI and GitHub Pages.

## Checked weighted-cosine arithmetic application

`import ComputableAnalysis.Cartwright` supplies two native derivations of the
uniform weighted-cosine moment evaluation and irrationality of the original
geometric pi squared. The optional `MathlibComparison.Cartwright` supplies a
third derivation of the identical native statements. See
`book/CARTWRIGHT_COMPLETE.md` for the constructed moment program, its successful
joint schedule, the arithmetic boundary, and the actual independence audit.
These are closed proofs, not uninhabited analytic providers.

### Paired Wallis and beta integral applications

Completed in the integral-portfolio continuation: uniform Wallis factorial
integrals and rational Wallis-product bounds for geometric pi; integer-beta
factorial integrals and polynomial density normalization. Each has a closed
native FTC proof and a Mathlib proof of the same computational proposition.
The independently validated schedules, exact declaration maps, and cumulative
post-Cartwright costs are exported by `ExportIntegralPortfolio.lean`.
The supported entry points are `ComputableAnalysis.IntegralApplications` and,
only in the optional comparison workspace, `MathlibComparison.IntegralApplications`.

## Current infrastructure cleanup

The quantitative tagged-dyadic quadrature certificate in
`QuadratureCertificate.lean` preserves integral meaning separately from number
validity. `QuadratureAdapters.lean` connects the existing rational-Lipschitz and
monotone sample algorithms to it. Legacy wrappers remain for compatibility;
general interval/partition/FTC adapter migration is not yet complete.

Routine calculations are disposable acceptance tests against unchanged native
sources. Retain reusable rules and a small set of specification regressions,
not every generated proof. See `FORMALIZATION_GUIDE.md` and
`book/checks/run_disposable_lean.py`. No new Mathlib comparison or complete
first-year-calculus release is asserted by this cleanup.
