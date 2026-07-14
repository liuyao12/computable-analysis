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

## Pi formalization scoreboard

A row counts as definition-complete only after its interval sequence is a valid
`RealRaw`.  A row counts as equivalent after a formalized chain of
`RealRaw.Equiv` theorems connects it to `piCircleArea`.

Current count: definitions `7/16`; equivalences `5/15` applicable rows.
Baseline equivalence: `piCircleArea` = N/A. Rendered copy:
[front page: pi scoreboard](https://liuyao12.github.io/computable-analysis/).

| Computation | Blueprint | Formula | Def. | Equiv. |
| --- | --- | --- | --- | --- |
| `piCircleArea` | [algorithm](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:circle-area-stage-algorithm), [validity](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#thm:geometric-pi-validity) | $a_{n+1}=a_n+\Delta_n,\ b_{n+1}=b_n-\nabla_n,\ \pi\in[4a_n,4b_n]$ | ✓ | N/A |
| `piCircleAreaPolygon` | [algorithm](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:circle-area-stage-algorithm), [finite Archimedes bridge](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#thm:finite-archimedes) | rational chord and tangent polygon fans | ✓ | ✓ |
| `piCircumference` | [algorithm](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:circle-circumference-stage-algorithm), [comparison](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#thm:finite-archimedes) | $\pi\in[L_n,U_n],\quad U_n-L_n\to0$ | ✗ | ✗ |
| **Arctangent routes** | [geom](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:arctan-area-stage-algorithm), [integral](https://liuyao12.github.io/computable-analysis/ch-integrals.html#def:arctan-integral), [series](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#def:arctan-series), [area](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:power-series-arctan-area-pi), [Machin](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:leibniz-machin) | $\pi=4\arctan(1)=4\int_0^1\frac{dt}{1+t^2}=4\sum_{k\ge0}\frac{(-1)^k}{2k+1}$ |  |  |
| `4 * arctanGeom(1)` | [definition](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:arctan-area-stage-algorithm), [equiv](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#thm:geometric-arctan-one-area-pi) | $\pi=4\,\arctan_{\mathrm{geom}}(1)$ | ✓ | ✓ |
| `4 * arctanIntegralRectangleForAtOne` | [rectangles](https://liuyao12.github.io/computable-analysis/ch-integrals.html#thm:finite-arctan-integral-comparison), [equiv](https://liuyao12.github.io/computable-analysis/ch-integrals.html#thm:arctan-integral-pi) | $\pi=4\int_0^1 \frac{dt}{1+t^2}$ | ✓ | ✓ |
| `4 * arctanSeries(1)` | [series](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#def:arctan-series), [endpoint](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:leibniz-arctan), [finite Riemann bridge](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:power-series-arctan-area-pi) | $\pi=4\sum_{k\ge0}\frac{(-1)^k}{2k+1}$ | ✓ | ✓ |
| `piMachin` | [series](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#def:arctan-series), [identity](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:machin-tangent), [finite bridge](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:leibniz-machin) | $\pi=4(4\arctan_{\mathrm{series}}(1/5)-\arctan_{\mathrm{series}}(1/239))$ | ✓ | ✓ |
| `6 * arcsinIntegral(1/2)` | [definition](https://liuyao12.github.io/computable-analysis/ch-integrals.html#def:inverse-elementary-integral-identities) | $\pi=6\arcsin(1/2)=6\int_0^{1/2}\frac{dx}{\sqrt{1-x^2}}$ | ✗ | ✗ |
| `NewtonSegmentPi` | [sources](https://liuyao12.github.io/computable-analysis/sect0002.html#rem:sources-of-raw-reals) | $\pi=12(\int_0^{1/2}\sqrt{1-x^2}\,dx-\sqrt3/8)$ | ✗ | ✗ |
| `GaussianPi` | [sources](https://liuyao12.github.io/computable-analysis/sect0002.html#rem:sources-of-raw-reals) | $\pi=\frac12(\int_{-\infty}^{\infty}e^{-x^2/2}\,dx)^2$ | ✗ | ✗ |
| `reciprocalQuarticMinusOneProjectiveRoute` | [kernel](https://liuyao12.github.io/computable-analysis/ch-integrals.html#def:reciprocal-quartic-test-kernel), [route](https://liuyao12.github.io/computable-analysis/ch-integrals.html#thm:reciprocal-quartic-route-package) | $\pi=\int_{-\infty}^{\infty}\frac{dx}{x^4-x^2+1}$ | ✗ | ✗ |
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
- Rectangle arctangent:
  `PiProofs.four_arctanIntegralRectangleForAtOne_equiv_piCircleArea`,
  `PiProofs.four_arctanIntegralRectangleMonotoneForAtOne_equiv_piCircleArea`,
  `IntegralIdentities.arctanIntegralRectangleUnitFunctionAgreement`.
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
