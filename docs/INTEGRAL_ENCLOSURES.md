# Integrals constructed from whole chunks

The defining computation for a particular function is a sum of certified
outer enclosures over whole chunks. Monotonicity often identifies the endpoint
bounds exactly. A function-specific interval estimate may serve the same role.
Neither pointwise evaluation nor the validity of an arbitrary output number
establishes an integral.

For a real chunk, multiply its range interval by its nonnegative length. For
a complex chunk, multiply its range rectangle by the finite oriented complex
displacement. Add the resulting intervals or rectangles. Certify coverage of
the entire domain, nesting (or justified finite intersections), and shrinking
widths. A parametrized formula is a comparison theorem, not the initial
segment definition. Known endpoint formulas and accelerated series remain
useful after a proved comparison to the enclosure sums.

## What the audit changed

- `Integral.CandidateFor` replaces the old two-field `ConstructionFor`;
  `candidateValue` replaces its unqualified `integralFor` accessor. The old
  integrand parameter was phantom: any valid number could be attached to it.
  Monotone and piecewise wrappers are now named as candidates too. Numerical
  validity is still proved, but it is not called evidence of integration.
- `Integral.SampleConstruction` and `sampleValue` replace the older sampled
  `Construction` and `integral`. A stationary sampling plan could produce a
  valid number without controlling the function between samples. These remain
  finite comparison tools, not a universal integration operator.
- `EndpointComparisonFor` replaces `DefiniteIdentityFor`: its fields compare
  a candidate with an endpoint expression. Function-specific range evidence
  remains essential; an arbitrary endpoint comparison alone does not supply it.
- Restricting a monotone candidate now requires a computation for the smaller
  interval. Previously the helper silently reused the full interval's number.
  The one-piece promotion still uses its original value, on the identical domain.
- `Integral.EnclosurePlanFor` stores the actual partition, whole-cell outer
  ranges, evaluation precision, and containment proof for the specified
  function. `EnclosureConstructionFor` computes their literal sums and
  certifies validity. Increasing, decreasing, and general interval-range
  schedules have adapters that retain the range evidence.
- `EnclosureRealizationFor` additionally permits a faster evaluator only with
  a comparison to shrinking, function-specific enclosure sums. The
  derivative-bound FTC adapter and a concrete arctangent instance are checked.
  This is not a universal existence assertion.
- `PolygonalIntegralCertificate` now requires soundness of its box evaluator,
  independently of output validity. The evaluator uses a positive dyadic mesh,
  starting with one chunk. The old empty first stage forced zero even on an
  open segment. Constant open paths now have a validity certificate; the
  square-polynomial evaluator has a whole-box soundness theorem.
- `VerticalReciprocalIntegral` now constructs the reciprocal integral on the
  upward unit segment directly. It proves coordinate monotonicity, whole-chunk
  containment, reciprocal semantics, nested dyadic sums, validity, and the exact
  coordinate widths \(2^{-n-1}\). No logarithm value or parametrized integral
  appears in its construction.
- The polynomial complex endpoint calculation is now named
  `polygonalPolynomialEndpointRaw`. Finite cancellation is preserved; a
  rectangle-integral interpretation needs a separate FTC bridge.
- Abelian path metadata and sampled sums are explicitly `ValueCandidate` and
  `SegmentSumCandidate`. They do not construct abelian integrals. The
  parametrized-arc data remain comparison targets.

No existing mathematical proof was replaced by an axiom or an unproved
assertion. Concrete finite identities and their hypotheses are preserved.
The migrations change the meaning advertised by the weak interfaces; they
are intentionally not kept as aliases named “integral”.

## Reading the remaining families

The inventory classifies every native module containing integration-related
text, plus the closely related square-pole module. Its declaration index is a
search aid, not a proof checker or an automatic theorem-status classifier.

| Role | Interpretation |
| --- | --- |
| `enclosure` | Whole-cell enclosures, their actual finite sums, or adapters retaining that evidence. |
| `comparison` | Function-specific endpoint, series, geometric, or finite-sum comparisons. Consult the individual theorem hypotheses and domains. |
| `mixed` | Both checked constructions and legacy candidates or conditional interfaces. No module-wide claim of integrability. |
| `conditional` | Analytic data supplied by a caller, quadrature reconstruction, or an unfinished integral interpretation. |
| `finite` | Finite polynomial, moment, recurrence, geometry, or quadrature algebra; no infinite integral inferred from its name. |
| `support` | Consumers, imports, tests, or function definitions that mention integrals without adding an integration rule. |

Monotone rectangles, Lipschitz-padded rectangles, turning-point gaps, finite
Stieltjes comparisons, and finite derivative-bound FTC are compatible routes.
A shrinking gap needs a range bound; an improper integral also needs a tail
bound. Irrational inputs and endpoints still require the represented-input
and domain bridges of the governing policy. The new rational-partition
adapters do not assert those bridges for every function automatically.

The Cauchy cancellation code proves convergence of its specified midpoint
computation from local affine approximation data. The square-pole code
compares common-tag reciprocal sums with arctangent rectangles. These checked
statements are retained. The corresponding native values are now named `quadrature` and
`residueQuadrature`, not integral definitions. Their agreement with independently refined
whole-chunk contour rectangles is a separate missing bridge; neither is
silently relabelled as a proof of that bridge. The general Cauchy integral
formula, the generic Cauchy-to-Taylor bridge, and general abelian integration
remain open. The direct reciprocal integral on the vertical unit segment is now constructed;
its exact comparison to the logarithm evaluator remains open.

Historical Lean snapshots under `book/` compile against their pinned source
and keep their historical interfaces. They are proof comparisons, not new
native integral definitions. The reader edition points to this current
convention and preserves their original proof provenance.

## Verification

Run `lake build ComputableAnalysis ComputableAnalysisBlueprint`,
`lake env lean scripts/check_integral_enclosures.lean`, and
`python3 scripts/audit_integral_enclosures.py`. The focused Lean checks cover
whole-cell range preservation, the restricted constant interval, the
arctangent realization, rotation of rectangle bounds, and the nonzero open
vertical segment at the first stage. The inventory checker rejects an
unclassified native module or a reintroduced weak public integral interface.

## Native source inventory

| Source | Role |
| --- | --- |
| [AbelianIntegrals.lean](../ComputableAnalysis/AbelianIntegrals.lean) | `conditional` |
| [AbsIntegral.lean](../ComputableAnalysis/AbsIntegral.lean) | `comparison` |
| [AlgebraicODE/FrobeniusTests.lean](../ComputableAnalysis/AlgebraicODE/FrobeniusTests.lean) | `support` |
| [AlgebraicODE/Fuchs.lean](../ComputableAnalysis/AlgebraicODE/Fuchs.lean) | `support` |
| [AlgebraicODE/Tests.lean](../ComputableAnalysis/AlgebraicODE/Tests.lean) | `support` |
| [Apery/Binomial.lean](../ComputableAnalysis/Apery/Binomial.lean) | `finite` |
| [Apery/Tests.lean](../ComputableAnalysis/Apery/Tests.lean) | `support` |
| [ArctanEffectiveFTC.lean](../ComputableAnalysis/ArctanEffectiveFTC.lean) | `comparison` |
| [ArctanGeometry.lean](../ComputableAnalysis/ArctanGeometry.lean) | `enclosure` |
| [ArctanRectanglePi.lean](../ComputableAnalysis/ArctanRectanglePi.lean) | `enclosure` |
| [ArctanTaylorConvergence.lean](../ComputableAnalysis/ArctanTaylorConvergence.lean) | `comparison` |
| [ArctanTaylorRemainder.lean](../ComputableAnalysis/ArctanTaylorRemainder.lean) | `comparison` |
| [Blueprint.lean](../ComputableAnalysis/Blueprint.lean) | `support` |
| [Calculus.lean](../ComputableAnalysis/Calculus.lean) | `mixed` |
| [CalculusFoundation.lean](../ComputableAnalysis/CalculusFoundation.lean) | `support` |
| [CauchyPi.lean](../ComputableAnalysis/CauchyPi.lean) | `comparison` |
| [CauchyTaylor.lean](../ComputableAnalysis/CauchyTaylor.lean) | `conditional` |
| [CauchyTaylorCoefficients.lean](../ComputableAnalysis/CauchyTaylorCoefficients.lean) | `conditional` |
| [CauchyTaylorExamples.lean](../ComputableAnalysis/CauchyTaylorExamples.lean) | `conditional` |
| [CauchyTaylorKernel.lean](../ComputableAnalysis/CauchyTaylorKernel.lean) | `finite` |
| [ComplexAnalysis/Cauchy.lean](../ComputableAnalysis/ComplexAnalysis/Cauchy.lean) | `conditional` |
| [ComplexAnalysis/Polygon.lean](../ComputableAnalysis/ComplexAnalysis/Polygon.lean) | `conditional` |
| [ComplexAnalysis/Residue.lean](../ComputableAnalysis/ComplexAnalysis/Residue.lean) | `conditional` |
| [ComplexAnalysis/ResidueExamples.lean](../ComputableAnalysis/ComplexAnalysis/ResidueExamples.lean) | `conditional` |
| [ComplexAnalysis/SquarePole.lean](../ComputableAnalysis/ComplexAnalysis/SquarePole.lean) | `conditional` |
| [ComplexIntegralEnclosure.lean](../ComputableAnalysis/ComplexIntegralEnclosure.lean) | `enclosure` |
| [ComplexLogarithmApproximation.lean](../ComputableAnalysis/ComplexLogarithmApproximation.lean) | `support` |
| [ComplexPathIntegral.lean](../ComputableAnalysis/ComplexPathIntegral.lean) | `mixed` |
| [Differential.lean](../ComputableAnalysis/Differential.lean) | `support` |
| [EffectiveCalculusFoundation.lean](../ComputableAnalysis/EffectiveCalculusFoundation.lean) | `support` |
| [EffectiveFourierSeries.lean](../ComputableAnalysis/EffectiveFourierSeries.lean) | `conditional` |
| [EffectiveFourierTail.lean](../ComputableAnalysis/EffectiveFourierTail.lean) | `conditional` |
| [Elementary.lean](../ComputableAnalysis/Elementary.lean) | `support` |
| [ElementaryFunctions.lean](../ComputableAnalysis/ElementaryFunctions.lean) | `support` |
| [ExpProofs.lean](../ComputableAnalysis/ExpProofs.lean) | `comparison` |
| [ExponentialLogarithmFoundation.lean](../ComputableAnalysis/ExponentialLogarithmFoundation.lean) | `support` |
| [FTC.lean](../ComputableAnalysis/FTC.lean) | `mixed` |
| [FiniteComplexPathCertificate.lean](../ComputableAnalysis/FiniteComplexPathCertificate.lean) | `mixed` |
| [FiniteFTCIntervalRegular.lean](../ComputableAnalysis/FiniteFTCIntervalRegular.lean) | `enclosure` |
| [FiniteGaussianIntegral.lean](../ComputableAnalysis/FiniteGaussianIntegral.lean) | `finite` |
| [FiniteNBallVolume.lean](../ComputableAnalysis/FiniteNBallVolume.lean) | `finite` |
| [FinitePiecewiseAbsoluteValue.lean](../ComputableAnalysis/FinitePiecewiseAbsoluteValue.lean) | `comparison` |
| [FinitePiecewiseRectangles.lean](../ComputableAnalysis/FinitePiecewiseRectangles.lean) | `enclosure` |
| [FinitePolynomialCalculus.lean](../ComputableAnalysis/FinitePolynomialCalculus.lean) | `finite` |
| [FiniteQuadratureMeanValue.lean](../ComputableAnalysis/FiniteQuadratureMeanValue.lean) | `finite` |
| [FiniteSecantIntegralOrder.lean](../ComputableAnalysis/FiniteSecantIntegralOrder.lean) | `finite` |
| [FiniteSineIntegral.lean](../ComputableAnalysis/FiniteSineIntegral.lean) | `finite` |
| [FiniteSinePrefixFTC.lean](../ComputableAnalysis/FiniteSinePrefixFTC.lean) | `comparison` |
| [FirstYearCalculus.lean](../ComputableAnalysis/FirstYearCalculus.lean) | `support` |
| [GeometryFoundation.lean](../ComputableAnalysis/GeometryFoundation.lean) | `support` |
| [IntegralEnclosure.lean](../ComputableAnalysis/IntegralEnclosure.lean) | `enclosure` |
| [IntegralEnclosureExamples.lean](../ComputableAnalysis/IntegralEnclosureExamples.lean) | `enclosure` |
| [IntegralFoundation.lean](../ComputableAnalysis/IntegralFoundation.lean) | `support` |
| [IntegralIdentities.lean](../ComputableAnalysis/IntegralIdentities.lean) | `mixed` |
| [IntegrationByPartsPi.lean](../ComputableAnalysis/IntegrationByPartsPi.lean) | `comparison` |
| [LeibnizPi.lean](../ComputableAnalysis/LeibnizPi.lean) | `comparison` |
| [LeibnizPiTaylor.lean](../ComputableAnalysis/LeibnizPiTaylor.lean) | `comparison` |
| [LeibnizTransmutation.lean](../ComputableAnalysis/LeibnizTransmutation.lean) | `comparison` |
| [Logarithm.lean](../ComputableAnalysis/Logarithm.lean) | `comparison` |
| [LogarithmicPi.lean](../ComputableAnalysis/LogarithmicPi.lean) | `comparison` |
| [PDE/CauchyContour.lean](../ComputableAnalysis/PDE/CauchyContour.lean) | `conditional` |
| [PeanoBaker.lean](../ComputableAnalysis/PeanoBaker.lean) | `finite` |
| [PiComplex.lean](../ComputableAnalysis/PiComplex.lean) | `support` |
| [PiProofs.lean](../ComputableAnalysis/PiProofs.lean) | `mixed` |
| [Playground.lean](../ComputableAnalysis/Playground.lean) | `support` |
| [PolynomialFTCValues.lean](../ComputableAnalysis/PolynomialFTCValues.lean) | `comparison` |
| [PowerSeries.lean](../ComputableAnalysis/PowerSeries.lean) | `finite` |
| [PrimitivePiecewiseFTC.lean](../ComputableAnalysis/PrimitivePiecewiseFTC.lean) | `conditional` |
| [QuarterCircleGeometry.lean](../ComputableAnalysis/QuarterCircleGeometry.lean) | `finite` |
| [RationalCircle.lean](../ComputableAnalysis/RationalCircle.lean) | `finite` |
| [RationalGeometry.lean](../ComputableAnalysis/RationalGeometry.lean) | `finite` |
| [ReciprocalQuarticPi.lean](../ComputableAnalysis/ReciprocalQuarticPi.lean) | `comparison` |
| [SectorAreaReparametrization.lean](../ComputableAnalysis/SectorAreaReparametrization.lean) | `comparison` |
| [SectorAreaRotation.lean](../ComputableAnalysis/SectorAreaRotation.lean) | `comparison` |
| [SeriesFoundation.lean](../ComputableAnalysis/SeriesFoundation.lean) | `support` |
| [SinPiIntegral.lean](../ComputableAnalysis/SinPiIntegral.lean) | `comparison` |
| [SinPiSquareFTC.lean](../ComputableAnalysis/SinPiSquareFTC.lean) | `comparison` |
| [TangentPullbackEffectiveFTC.lean](../ComputableAnalysis/TangentPullbackEffectiveFTC.lean) | `comparison` |
| [Taylor.lean](../ComputableAnalysis/Taylor.lean) | `conditional` |
| [TurningPointIntegral.lean](../ComputableAnalysis/TurningPointIntegral.lean) | `mixed` |
| [WiedijkScoreboard.lean](../ComputableAnalysis/WiedijkScoreboard.lean) | `support` |
| [ZetaReal/Moments.lean](../ComputableAnalysis/ZetaReal/Moments.lean) | `finite` |
| [ZetaReal/Series.lean](../ComputableAnalysis/ZetaReal/Series.lean) | `finite` |
| [ZetaReal/Tests.lean](../ComputableAnalysis/ZetaReal/Tests.lean) | `support` |
| [ComplexAnalysis/Examples.lean](../ComputableAnalysis/ComplexAnalysis/Examples.lean) | `conditional` |
| [VerticalReciprocalIntegral.lean](../ComputableAnalysis/VerticalReciprocalIntegral.lean) | `enclosure` |
