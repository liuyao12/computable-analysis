# Computable Analysis

*calculus without the completeness of the real numbers*

This project is about proof-facing computable analysis, not building a
general floating-point or numerical-functions library. Existing numerical
libraries are already the right tool when the goal is fast computation.

The goal here is to express transparent rational interval algorithms in Lean,
prove their validity and equivalence, and package certificates that can be
used inside other mathematics proofs or in science and engineering arguments.
We prefer simple, inspectable constructions and clear proof obligations over
being as fast as possible.

See `GOALS.md` for the current mathematical roadmap and links to the Lean
definitions/proved bridge theorems.

## Linear differential equations

The foundation now has a finite Peano--Baker entry point in
`ComputableAnalysis/PeanoBaker.lean`: rational matrices, sampled linear
systems, and an executable noncommutative ordered-word expansion. The finite
identity between that expansion and the chronological Euler product is proved,
as is a discrete variation-of-constants decomposition for the inhomogeneous
recurrence. Constant increments reduce exactly to `(I + B)^N`, while the zero
coefficient case is the identity. A square-zero sampled coefficient family
reduces exactly to `I + sum B_k`, so the finite word series already covers a
nontrivial nilpotent case. Local matrix associativity and a chronological
product-splitting law are proved; pairwise-commuting increments now commute
with their accumulated finite transition. Its
continuous successor will solve `x' = A(t)x + b(t)` by certified simplex
integrals and factorial tail bounds, beginning with constant, commuting,
scalar, piecewise-constant, and higher-order triangular cases. This broadens
the calculus foundation. The Pi integration suite records which independent
capabilities its checked routes exercise; it intentionally has no completion
fraction for calculus.

## Calculus readiness ledger

The Pi table below is deliberately an integration suite, not the project
score.  It is good at detecting that independently developed finite geometry,
series, integration, and inverse-function bridges agree on one demanding
constant.  It is not a good proxy for the ability to formulate and solve a
new scientific model: several Pi rows can share the same arctangent bridge,
while a major advance such as a continuous Peano--Baker theorem need not move
the Pi count at all.

We therefore use the following gates for the actual calculus goal.  A gate is
marked **checked** only for the stated end-to-end theorem, not merely because
the vocabulary for it exists.  There is intentionally no single percentage:
the gates have different dependencies and none can substitute for another.

| Gate | Current checked boundary | Next boundary |
| --- | --- | --- |
| Rational interval foundation | `RealRaw.Valid`, equivalence by overlap, and the no-completeness/no-Mathlib-analysis audit | Continue dependency auditing as modules grow |
| Continuity and extension | `IntervalRegularOn.epsilonDeltaContinuous` gives literal rational $\varepsilon$--$\delta$ continuity; scheduled `sqrtOnUnit` is a checked non-exact interval-regular example with a quadratic modulus | Representation-respecting extension needs general closure theorems, beyond the current certified-extension interface |
| Finite integration and FTC | Certified integral constructions, finite geometric integration by parts with increasing/decreasing-piece corner bounds, and certificate-to-endpoint FTC bridges are checked; concrete rectangle and compactified Cauchy/quartic integrals run end to end | A broadly reusable construction from interval regularity and derivative certificates for standard functions |
| Monotone inverse functions | Branch-local inverse API and bisection are checked; `sqrt` supplies the concrete unit-interval rational-target example | General represented targets, then sine/arcsine and exponential/logarithm branches |
| Differentiated elementary functions | Formal power-series derivative table and finite-difference affine/square examples are checked | An analytic certificate that the chosen exponential has derivative itself, followed by log/exp identities |
| Linear ODEs | Finite Peano--Baker, chronological products, and discrete variation of constants are checked | Interval-matrix simplex integrals, factorial tails, and continuous variation of constants |

The Pi suite remains useful as a secondary release test: add a row only when
it exercises a genuinely new foundation or a new end-to-end bridge.  Do not
inflate it with presentation variants of the same arctangent construction.
The checked registry records its primary coverage family in Lean as
`PiProofs.PiPresentation.integrationFamily`; that makes the shared
dependencies explicit instead of turning the number of presentation variants
into a progress percentage.

## Pi registry coverage suite

`PiProofs.PiCoverageBridge` is a supporting registry, not the public list of
pi formulas.  It has one constructor for each distinct end-to-end bridge, and
its `equivalent` theorem checks both sides as valid `RealRaw` computations and
proves their `RealRaw.Equiv` relation.  Public chapters instead state natural
theorems such as an integral evaluation or the Basel identity; registry
agreement is a derived corollary.  This is evidence for a calculus
capability—not a percentage for the whole foundation.

| Natural theorem family | Checked registry role |
| --- | --- |
| finite Archimedean theorem | perimeter and area presentations agree |
| arctangent power-series theorem | geometric and series presentations agree |
| arctangent integral evaluation | integral and series presentations agree |
| Cauchy integral evaluation | full-line integral and area presentations agree |
| reciprocal-quartic integral evaluation | quartic and Cauchy integral presentations agree |

This deliberately does not measure the primary application gaps: an
exponential raw with `d/dx exp = exp`, reusable derivative/FTC constructions,
or the continuous matrix Peano--Baker theorem would each be major progress
without adding a π equivalence.  Rendered copy:
[front page: π equivalence coverage](https://liuyao12.github.io/computable-analysis/).

The next intended π registry benchmark is the arctangent
integration-by-parts evaluation, not another arctangent variant.  Its public
statement will be the natural integral formula; its derived presentation
agreement will become a sixth coverage bridge only after the
product/derivative/FTC route, its common monotone-piece refinement, and the
logarithm endpoint identity are all checked.  The uniform-grid core of that
refinement is now formalized: the `m*n` rational grid explicitly contains
both the `m` and `n` grids, and its mesh is the old width divided by the
positive factor.  The two embeddings are packaged as a checked
`CommonRefinement` certificate.  General piecewise synchronization now has a
checked arbitrary-breakpoint insertion primitive: `locateInsertionCell` scans
the finite partition to select and certify an enclosing cell, and
`insertionChainOfPointList` turns any finite in-range rational list into a
composable sequence of those insertions.  The remaining step is a canonical
merge that retains the two independently supplied breakpoint-list embeddings.
The dyadic stages used by existing Riemann
algorithms now have direct point-preservation and mesh-halving theorems as
well.  The finite corner correction now has a checked rational vanishing
schedule on the unit mesh: it is exactly `1/n`, hence at most a requested
positive epsilon at `n = epsilon.den + 1`.

The direct chord-path route now also has a checked
`piCircumferenceStabilized` representative. It evaluates only a finite prefix
of widened chord-path intervals, using the public rational modulus `4/(n+1)`;
the area loop is used only in the proof that this radius is sound. This is a
useful general interval-normalization bridge, but deliberately not a new
coverage bridge: it does not prove the original `piCircumference` endpoints
refine stage by stage.

The direct proof has a sharper checked boundary: the rational curvature chord
certificate is converted to a bisection lower bound with its explicit width
loss, and `AdjacentChordCurvatureMarginCoversFineWidths` states the sole
remaining finite margin inequality.  Its implication to the original local
endpoint-refinement condition is formalized; the universal margin proof is
still open.

The useful output of the completed rows is now formalized as a registry rather
than another percentage. `PiProofs.piCertified : Real` uses `piCircleArea` as
its preferred evaluator and retains each canonical completed route as a
certified equivalent alternative. `PiProofs.PiPresentation` gives those
routes stable names, and `PiProofs.piCertifiedPresentation` retrieves a named
`Real.Representation`. This includes the geometry, stabilized circumference,
single Machin, Leibniz, Nilakantha, rectangle, Cauchy, and reciprocal-quartic
routes, together with the two certified perimeter normalizations; it excludes
unproved rows and arbitrary presentation variants.

### Full implementation inventory

The following longer table preserves every checked implementation and future
probe.  It is a regression inventory, not the progress board: Machin is the
single power-series formula, while Nilakantha and the normalization variants
are supplementary tests; the direct perimeter, arcsine/Newton, and Gaussian
entries diagnose future calculus gates.  Basel, Brouncker, and logarithm at
`i` are advanced-analysis entries, not scientific-calculus prerequisites.

| Computation | Blueprint | Formula | Def. | Equiv. |
| --- | --- | --- | --- | --- |
| `piCircleArea` | [algorithm](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:circle-area-stage-algorithm), [validity](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#thm:geometric-pi-validity) | $a_{n+1}=a_n+\Delta_n,\ b_{n+1}=b_n-\nabla_n,\ \pi\in[4a_n,4b_n]$ | ✓ | N/A |
| `piCircleAreaPolygon` | [algorithm](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:circle-area-stage-algorithm), [finite Archimedes bridge](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#thm:finite-archimedes) | rational chord and tangent polygon fans | ✓ | ✓ |
| `piCircumference` | [algorithm](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:circle-circumference-stage-algorithm), [comparison](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#thm:finite-archimedes) | $\pi\in[L_n,U_n],\quad U_n-L_n\to0$ | ✗ | ✗ |
| `piCircumferenceFan` | [algorithm](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:circle-circumference-stage-algorithm), [finite Archimedes bridge](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#thm:finite-archimedes) | exact inscribed cross-fan lower bound with circumscribed polygonal upper bound | ✓ | ✓ |
| **Arctangent routes** | [geom](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:arctan-area-stage-algorithm), [integral](https://liuyao12.github.io/computable-analysis/ch-integrals.html#def:arctan-integral), [series](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#def:arctan-series), [area](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:power-series-arctan-area-pi), [Machin](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:leibniz-machin) | $\pi=4\arctan(1)=4\int_0^1\frac{dt}{1+t^2}=4\sum_{k\ge0}\frac{(-1)^k}{2k+1}$ |  |  |
| `4 * arctanGeom(1)` | [definition](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:arctan-area-stage-algorithm), [equiv](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#thm:geometric-arctan-one-area-pi) | $\pi=4\,\arctan_{\mathrm{geom}}(1)$ | ✓ | ✓ |
| `4 * arctanIntegralRectangleForAtOne` | [rectangles](https://liuyao12.github.io/computable-analysis/ch-integrals.html#thm:finite-arctan-integral-comparison), [equiv](https://liuyao12.github.io/computable-analysis/ch-integrals.html#thm:arctan-integral-pi) | $\pi=4\int_0^1 \frac{dt}{1+t^2}$ | ✓ | ✓ |
| `4 * arctanSeries(1)` | [series](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#def:arctan-series), [endpoint](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:leibniz-arctan), [finite Riemann bridge](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:power-series-arctan-area-pi) | $\pi=4\sum_{k\ge0}\frac{(-1)^k}{2k+1}$ | ✓ | ✓ |
| `piNilakantha` | [finite series transformation](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:nilakantha-pi) | $\pi=3+\frac4{2\cdot3\cdot4}-\frac4{4\cdot5\cdot6}+\frac4{6\cdot7\cdot8}-\cdots$ | ✓ | ✓ |
| `piMachin` | [series](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#def:arctan-series), [identity](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:machin-tangent), [finite bridge](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:leibniz-machin) | $\pi=4(4\arctan_{\mathrm{series}}(1/5)-\arctan_{\mathrm{series}}(1/239))$ | ✓ | ✓ |
| `6 * arcsinIntegral(1/2)` | [definition](https://liuyao12.github.io/computable-analysis/ch-integrals.html#def:inverse-elementary-integral-identities) | $\pi=6\arcsin(1/2)=6\int_0^{1/2}\frac{dx}{\sqrt{1-x^2}}$ | ✗ | ✗ |
| `NewtonSegmentPi` | [sources](https://liuyao12.github.io/computable-analysis/sect0002.html#rem:sources-of-raw-reals) | $\pi=12(\int_0^{1/2}\sqrt{1-x^2}\,dx-\sqrt3/8)$ | ✗ | ✗ |
| `GaussianPi` | [sources](https://liuyao12.github.io/computable-analysis/sect0002.html#rem:sources-of-raw-reals) | $\pi=\frac12(\int_{-\infty}^{\infty}e^{-x^2/2}\,dx)^2$ | ✗ | ✗ |
| `cauchyFullLineIntegral` | [reciprocal-tail compactification](https://liuyao12.github.io/computable-analysis/ch-integrals.html#def:reciprocal-tail-compactification) | $\pi=\int_{-\infty}^{\infty}\frac{dx}{1+x^2}$, represented by a finite reciprocal-tail chart | ✓ | ✓ |
| `piReciprocalQuarticCompact` | [kernel](https://liuyao12.github.io/computable-analysis/ch-integrals.html#def:reciprocal-quartic-test-kernel), [route](https://liuyao12.github.io/computable-analysis/ch-integrals.html#thm:reciprocal-quartic-route-package) | $\pi=\int_{-1}^{1}\frac{1+x^2}{x^4-x^2+1}\,dx$ | ✓ | ✓ |
| `baselSeriesRaw` / `pi^2/6` | [definition](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#def:zeta-two-raw), [RHS valid](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:basel-geometric-rhs-valid) | $\zeta(2)=\sum_{n\ge1}\frac1{n^2}=\pi^2/6$ | ✓ | ✗ |
| `Brouncker(4/pi)` | [sources](https://liuyao12.github.io/computable-analysis/sect0002.html#rem:sources-of-raw-reals) | $\frac4\pi=1+\cfrac{1^2}{2+\cfrac{3^2}{2+\cfrac{5^2}{2+\cdots}}}$ | ✗ | ✗ |
| **Logarithm-at-i routes** | [overview](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:log-at-i-pi-routes), [series](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#def:complex-log-series-at-i), [path](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#def:complex-log-path-integral-at-i), [inverse](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#def:complex-log-inv-exp-at-i), [Euler](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:euler-identity) | $\exp(i\pi/2)=i,\quad \log(i)=i\pi/2,\quad \pi=-2i\log(i)$ |  |  |
| `-2i * logSeries(i)` | [series](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#def:complex-log-series-at-i), [route](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:log-at-i-pi-routes), [Euler](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:euler-identity) | $\pi=-2i\,\log_{\mathrm{series}}(i)$ | ✗ | ✗ |
| `-2i * logPathIntegral(i)` | [path](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#def:complex-log-path-integral-at-i), [route](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:log-at-i-pi-routes) | $\pi=-2i\int_{\gamma:1\to i}\frac{dz}{z}$ | ✗ | ✗ |
| `-2i * logInvExp(i)` | [inverse](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#def:complex-log-inv-exp-at-i), [route](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:log-at-i-pi-routes), [Euler](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:euler-identity) | $\pi=-2i\,\log_{\exp^{-1}}(i)$ | ✗ | ✗ |

Lean hooks:

- `piCircleArea`: `PiProofs.AreaLoopValidity.areaValid`,
  `PiProofs.four_arctanGeom_one_equiv_piCircleArea`.
- Unit arctangent: `ArctanGeometry.arctanGeom_valid_on_unit`,
  `ArctanGeometry.arctanGeom_valid_on_powerSeriesDomain`.
- Generic arctangent bridge: `PiProofs.arctanEqualsGeom_finiteRiemannBridge`.
  It supports the series-to-geometry comparison but is not a separate pi-scoreboard route.
- Nilakantha series: `piNilakantha`, `Nilakantha.compute_width_eq`,
  `Nilakantha.valid`, `Nilakantha.equiv_piLeibniz`, and
  `PiProofs.piNilakantha_equiv_piCircleArea`.  This is a direct rational
  series row; its finite summation transform uses the Leibniz endpoints only
  to identify the value, rather than treating it as a second Machin formula.
- Rectangle arctangent:
  `PiProofs.four_arctanIntegralRectangleForAtOne_equiv_piCircleArea`,
  `PiProofs.four_arctanIntegralRectangleMonotoneForAtOne_equiv_piCircleArea`,
  `IntegralIdentities.arctanIntegralRectangleUnitFunctionAgreement`.
- Reciprocal-tail Cauchy integral:
  `IntegralIdentities.ReciprocalTailCompactification`,
  `IntegralIdentities.cauchyFullLineIntegral_valid`,
  `PiProofs.cauchyFullLineIntegral_equiv_piCircleArea`.
- Old point-Riemann arctangent:
  `IntegralIdentities.arctanIntegral_compute_width_zero`,
  `IntegralIdentities.arctanIntegral_stages_constant`.
  This legacy wrapper is kept for conditional FTC bridge statements, but it is
  not a separate scoreboard row because it has no canonical standalone
  refining computation.
- Static dyadic integral API:
  `Integral.staticDyadicSubdivisions`, `Integral.staticDyadicPlan`,
  `Integral.staticDyadicAlgorithm`, `StaticDyadicEffectiveFTC`,
  `FTC.EndpointScheduleAgreement`,
  `FTC.endpointScheduleAgreement_of_effectiveFTC_stageSchedule`,
  `FTC.endpointScheduleAgreement_of_staticDyadicEffectiveFTC_stageSchedule`,
  `FTC.staticDyadicEffectiveFTC_definiteIntegralEqualsEndpoint`,
  `FTC.staticDyadicEffectiveFTC_definiteIntegralEqualsEndpoint_of_endpointAgreement`,
  `Integral.definiteIdentity_of_staticDyadicEffectiveFTC`,
  `Integral.definiteIdentity_of_staticDyadicEffectiveFTC_endpointAgreement`,
  `PiProofs.piFromArctanIntegral_equiv_piCircleArea_of_staticDyadicEffectiveFTC`,
  `PiProofs.piFromArctanIntegralFor_equiv_piCircleArea_of_staticDyadicEffectiveFTC`,
  `PiProofs.piFromArctanIntegralFor_equiv_piCircleArea_of_staticDyadicEffectiveFTC_stageSchedule`.
- Constant integral sanity laws:
  `Integral.constantIntegral_add_equiv`,
  `Integral.constantIntegral_scaleRat_equiv`,
  `Integral.constantIntegral_adjacent_additive`.
- Monotone-first integral API:
  `NondecreasingOnInterval`, `NonincreasingOnInterval`,
  `MonotoneOnInterval`, `MonotoneOnInterval.ofNondecreasing`,
  `MonotoneOnInterval.restrict`, `NondecreasingOnInterval.restrict`,
  `NonincreasingOnInterval.restrict`,
  `Integral.NondecreasingConstructionFor`,
  `Integral.NondecreasingConstructionFor.restrict`,
  `Integral.nondecreasingIntegralFor_valid`,
  `Integral.MonotoneConstructionFor`, `Integral.MonotoneConstructionFor.restrict`,
  `Integral.monotoneIntegralFor_valid`,
  `Integral.PiecewiseMonotoneConstructionFor`,
  `Integral.PiecewiseMonotoneConstructionFor.ofMonotone`,
  `Integral.PiecewiseMonotoneConstructionFor.ofNondecreasing`,
  `Integral.piecewiseMonotoneIntegralFor_valid`,
  `Integral.piecewiseMonotoneIntegralFor_ofMonotone_equiv`,
  `Integral.piecewiseMonotoneIntegralFor_ofNondecreasing_equiv`,
  `Integral.GeneralConstructionFor`, `Integral.generalIntegralFor_valid`,
  `Integral.generalIntegralFor_ofMonotone_equiv`,
  `Integral.generalIntegralFor_ofNondecreasing_equiv`,
  `FunctionOnInterval.PointwiseLe`,
  `Integral.LinearFor`,
  `Integral.CompatibleWithScaleRatFor`,
  `Integral.AdditiveOnAdjacentIntervalsFor`, `Integral.OrderPreservingFor`,
  `Integral.BasicPropertiesFor`,
  `Integral.PiecewiseMonotoneLinearFor`,
  `Integral.PiecewiseMonotoneCompatibleWithScaleRatFor`,
  `Integral.PiecewiseMonotoneAdditiveOnAdjacentIntervalsFor`,
  `Integral.PiecewiseMonotoneOrderPreservingFor`,
  `Integral.PiecewiseMonotoneBasicPropertiesFor`,
  `Integral.GeneralOrderPreservingFor`,
  `Integral.GeneralBasicPropertiesFor`,
  `RealRaw.sub_add_sub_cancel_middle_equiv`,
  `RealRaw.scaleRat_valid`, `RealRaw.scaleRat_equiv`,
  `endpointDifferenceRaw_adjacent_additive`,
  `FunctionOnInterval.endpointDifferenceRaw_adjacent_additive`,
  `Integral.DefiniteIdentityFor.integral_add_equiv_of_endpoint_additive`,
  `Integral.MonotoneDefiniteIdentityFor.integral_add_equiv_of_endpoint_additive`,
  `Integral.DefiniteIdentityFor.integral_equiv_add_of_endpoint_add`,
  `Integral.MonotoneDefiniteIdentityFor.integral_equiv_add_of_endpoint_add`,
  `Integral.DefiniteIdentityFor.integral_scaleRat_equiv_of_endpoint_scaleRat`,
  `Integral.MonotoneDefiniteIdentityFor.integral_scaleRat_equiv_of_endpoint_scaleRat`,
  `Integral.DefiniteIdentityFor.integral_le_of_endpoint_le`,
  `Integral.MonotoneDefiniteIdentityFor.integral_le_of_endpoint_le`,
  `Integral.MonotoneDefiniteIdentityFor`,
  `Integral.GeneralDefiniteIdentityFor`,
  `Integral.GeneralDefiniteIdentityFor.toDefiniteIdentityFor`,
  `Integral.GeneralDefiniteIdentityFor.transportConstruction`,
  `Integral.GeneralDefiniteIdentityFor.ofDefiniteIdentityFor`,
  `Integral.GeneralDefiniteIdentityFor.integral_equiv_integral`,
  `Integral.GeneralDefiniteIdentityFor.integral_add_equiv_of_endpoint_additive`,
  `Integral.GeneralDefiniteIdentityFor.integral_equiv_add_of_endpoint_add`,
  `Integral.GeneralDefiniteIdentityFor.integral_scaleRat_equiv_of_endpoint_scaleRat`,
  `Integral.GeneralDefiniteIdentityFor.integral_le_of_endpoint_le`,
  `Integral.GeneralDefiniteIdentityFor.ofMonotone`,
  `IntegralIdentities.arctanKernelIntervalAtOne_monotone`,
  `IntegralIdentities.arctanIntegralRectangleMonotoneForAtOne`,
  `IntegralIdentities.arctanIntegralRectangleMonotoneFunctionAgreement`,
  `IntegralIdentities.arctanGeomUnitRectangleMonotoneDefiniteIdentity`,
  `IntegralIdentities.arctanGeomUnitRectangleGeneralDefiniteIdentity`,
  `PiProofs.piFromArctanIntegralFor_equiv_piCircleArea_of_monotoneDefiniteIdentityFor`,
  `PiProofs.piFromArctanGeneralIntegralFor_equiv_piCircleArea_of_generalDefiniteIdentityFor`,
  `PiProofs.piFromArctanGeneralIntegralFor_equiv_piCircleArea_of_definiteIdentityFor_generalConstruction`,
  `PiProofs.piFromArctanGeomUnitRectangleGeneralDefiniteIdentity_equiv_piCircleArea`.
- FTC bridge to domain-aware integral identities:
  `Integral.DefiniteIdentityFor.transportConstruction`,
  `Integral.definiteIdentityFor_of_effectiveFTC`,
  `Integral.definiteIdentityFor_of_effectiveFTC_endpointAgreement`,
  `Integral.definiteIdentityFor_of_effectiveFTC_stageSchedule`,
  `Integral.generalDefiniteIdentityFor_of_effectiveFTC_stageSchedule`,
  `Integral.definiteIdentityFor_of_staticDyadicEffectiveFTC`,
  `Integral.definiteIdentityFor_of_staticDyadicEffectiveFTC_endpointAgreement`,
  `Integral.definiteIdentityFor_of_staticDyadicEffectiveFTC_stageSchedule`,
  `Integral.generalDefiniteIdentityFor_of_staticDyadicEffectiveFTC_stageSchedule`,
  `endpointDifference_valid_of_fun_valid`,
  `FTC.endpointScheduleAgreement_of_derivativeBoundFTC_stageSchedule`,
  `FTC.endpointScheduleAgreement_of_candidateDerivativeFTC_stageSchedule`,
  `FTC.endpointScheduleAgreement_of_curvatureFTC_stageSchedule`,
  `FTC.endpointScheduleAgreement_of_convexFTC_stageSchedule`,
  `FTC.endpointScheduleAgreement_of_concaveFTC_stageSchedule`,
  `derivativeBoundFTC`, `candidateDerivativeFTC`,
  `CurvatureFTCCertificate`, `curvatureFTC`,
  `ConvexFTCCertificate`, `convexFTC`,
  `ConcaveFTCCertificate`, `concaveFTC`,
  `Integral.definiteIdentityFor_of_derivativeBoundFTC`,
  `Integral.definiteIdentityFor_of_derivativeBoundFTC_endpointAgreement`,
  `Integral.definiteIdentityFor_of_derivativeBoundFTC_stageSchedule`,
  `Integral.generalDefiniteIdentityFor_of_derivativeBoundFTC_stageSchedule`,
  `Integral.definiteIdentityFor_of_candidateDerivativeFTC`,
  `Integral.definiteIdentityFor_of_candidateDerivativeFTC_endpointAgreement`,
  `Integral.definiteIdentityFor_of_candidateDerivativeFTC_stageSchedule`,
  `Integral.generalDefiniteIdentityFor_of_candidateDerivativeFTC_stageSchedule`,
  `Integral.definiteIdentityFor_of_curvatureFTC`,
  `Integral.definiteIdentityFor_of_curvatureFTC_endpointAgreement`,
  `Integral.definiteIdentityFor_of_curvatureFTC_stageSchedule`,
  `Integral.generalDefiniteIdentityFor_of_curvatureFTC_stageSchedule`,
  `Integral.definiteIdentityFor_of_convexFTC`,
  `Integral.definiteIdentityFor_of_convexFTC_endpointAgreement`,
  `Integral.definiteIdentityFor_of_convexFTC_stageSchedule`,
  `Integral.generalDefiniteIdentityFor_of_convexFTC_stageSchedule`,
  `Integral.definiteIdentityFor_of_concaveFTC`,
  `Integral.definiteIdentityFor_of_concaveFTC_endpointAgreement`,
  `Integral.definiteIdentityFor_of_concaveFTC_stageSchedule`,
  `Integral.generalDefiniteIdentityFor_of_concaveFTC_stageSchedule`,
  `PiProofs.piFromArctanIntegralFor_equiv_piCircleArea_of_effectiveFTC_stageSchedule`,
  `PiProofs.piFromArctanIntegralFor_equiv_piCircleArea_of_candidateDerivativeFTC_stageSchedule`,
  `PiProofs.piFromArctanIntegralFor_equiv_piCircleArea_of_curvatureFTC_stageSchedule`,
  `PiProofs.piFromArctanIntegralFor_equiv_piCircleArea_of_convexFTC_stageSchedule`,
  `PiProofs.piFromArctanIntegralFor_equiv_piCircleArea_of_concaveFTC_stageSchedule`.
Series target:

$$
\forall\,0\le p\le r\le1,\qquad
\frac{r-p}{1+r^2}\le
\int_p^r\sum_{j=0}^{2N}(-1)^jx^{2j}\,dx,\qquad
\int_p^r\sum_{j=0}^{2N+1}(-1)^jx^{2j}\,dx
\le
\frac{r-p}{1+p^2}.
$$

Uniform cell certificates through
$1-x^2+\cdots+x^{20}$,
$1-x^2+\cdots-x^{22}$:
`PiProofs.LeibnizRectangleBridge.evenKernelCellBound_ten`,
`PiProofs.LeibnizRectangleBridge.oddKernelUnitCellBound_eleven`.
Finite unit-cell package through the same prefix:
`PiProofs.LeibnizRectangleBridge.leibnizRectangleUniformUnitCellBoundsAtOneUpToFive`,
with transport to finite cell, kernel, raw-overlap, and scaled-route overlap targets.
Finite stage regression:
`PiProofs.LeibnizRectangleBridge.leibnizRectangleKernelCellBoundsAtOneUpToFifteen`,
`PiProofs.leibnizRectangleRawAtOneOverlapsUpToFifteen`,
`PiProofs.fourArctanSeriesRectangleRouteOverlapsUpToFifteen`.
Unit-cell scaled-route corollary:
`PiProofs.fourArctanSeriesRectangleRouteOverlapsUpToFive_of_unitUniform`.
All finite unit-cell prefixes now feed the full table route through
`PiProofs.four_arctanSeries_one_equiv_piCircleArea_of_unitUniformCellBoundsUpToAll`
and `PiProofs.leibnizEqArea_of_unitUniformCellBoundsUpToAll`.
The all-prefix conditions are named and reversible for the unit-cell, cell,
kernel, raw-overlap, and scaled-route layers, so future certificates can enter
the proof chain at the most convenient finite expression.
Sharper unit-cell bridge:
`PiProofs.LeibnizRectangleBridge.LeibnizRectanglePointwiseUnitIntegralBridgeAtOne`,
`PiProofs.four_arctanSeries_one_equiv_piCircleArea_of_pointwiseUnitIntegralBridge`.
Calculus-facing order target:
`Integral.ExactCellOrderPreservation`,
`PiProofs.LeibnizRectangleBridge.KernelPartialExactCellOrderPreservationOnUnit`,
`PiProofs.LeibnizRectangleBridge.unitCellOrderPreservation_of_kernelPartialExactCellOrderPreservation`,
`PiProofs.LeibnizRectangleBridge.LeibnizRectangleUnitCellOrderPreservation`,
`PiProofs.LeibnizRectangleBridge.pointwiseUnitIntegralBridgeAtOne_of_unitCellOrderPreservation`,
`PiProofs.four_arctanSeries_one_equiv_piCircleArea_of_kernelPartialExactCellOrderPreservation`,
`PiProofs.four_arctanSeries_one_equiv_piCircleArea_of_unitCellOrderPreservation`,
`PiProofs.leibnizEqArea_of_kernelPartialExactCellOrderPreservation`,
`PiProofs.leibnizEqArea_of_unitCellOrderPreservation`.

A complementary all-degree route now begins with exact rational Riemann
algebra in `Taylor.ArctanKernel`: `powDifferenceFactor` proves the
finite factorization of `r^n-p^n`,
`monomialIntegralBetween_endpoint_bounds` brackets each exact monomial
primitive by its endpoint rectangles, and
`monomialIntegralBetween_endpoint_error_le` bounds either endpoint error by
`k * (r-p)^2` on a unit cell.  This does not yet establish the Leibniz
equivalence; the remaining work is finite alternating-polynomial summation
over the existing dyadic square-mesh budget.

Circumference target:

$$
L_n\le L_{n+1}\le U_{n+1}\le U_n,\qquad U_n-L_n\to0.
$$

Shrinkage: `PiProofs.circumferenceWidthsShrink`.
Comparison target: `PiProofs.CircumferenceQuarterLengthRemainders`.
All finite refinement prefixes now feed validity through
`PiProofs.circumferenceValid_of_quarterLengthStepRefinesUpToAll`.
The finite-prefix and global refinement predicates are linked by
`PiProofs.circumferenceQuarterLengthStepRefines_iff_upToAll` and
`PiProofs.circumferenceStepRefines_iff_upToAll`, with a direct completion
package `PiProofs.CompletionCircumferenceQuarterLengthUpToAllRemainders`.

Reciprocal quartic algebra:

$$
\int_{-\infty}^{\infty}\frac{dx}{x^4-x^2+1}
=
\int_{-\infty}^{\infty}\frac{du}{1+u^2}
=\pi.
$$

Expected-value route:
`PiProofs.reciprocalQuarticMinusOneExpectedPi_equiv_piCircleArea`.
Scoreboard target: `ReciprocalQuarticMinusOneProjectiveRoute`.

When asked for the pi score, reproduce this table and update the counts if the
Lean formalization has moved.

## Blueprint

The rendered blueprint is available at
[liuyao12.github.io/computable-analysis](https://liuyao12.github.io/computable-analysis/).

The LaTeX blueprint lives in `blueprint/`.  It is
organized around the computable-real foundations, the effective FTC, the FTA,
and classical pre-completeness results such as Archimedes' pi, Leibniz/Machin,
Taylor expansions, and Basel.

To build it from the repository root:

```bash
python -m pip install -r blueprint/requirements.txt
leanblueprint web
leanblueprint serve
```

The rendered blueprint is produced by the `Build blueprint pages` workflow.
Pull requests that touch the blueprint run `leanblueprint web` as a render
check.  The public GitHub Pages site is deployed from that same workflow after
a merge or push to the repository default branch, or by manually running the
workflow from the Actions tab.
The generated `blueprint/web` directory is a build artifact and should not be
committed.
