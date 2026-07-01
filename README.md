# ComputableAnalysis

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

A pi computation counts as completed only after its interval sequence is
verified as a valid `RealRaw`: ordered intervals, nested sequence, and widths
shrinking to zero.  Equivalence counts when there is a formalized chain of
`RealRaw.Equiv` theorems connecting the computation to `piCircleArea`.
For formula rows that compute a related quantity first, such as `zeta(2)` or
`sqrt(2*pi)`, the definition column records whether that displayed interval
algorithm is verified, while the equivalence column records whether the pi
formula has been connected back to `piCircleArea`.

Current count: definitions completed `6/15`; equivalences to `piCircleArea`
formalized `2/14` applicable rows.  The baseline row `piCircleArea` is `N/A`
for equivalence scorekeeping.  The rendered scoreboard is in
[Ch. 8: pi scoreboard](https://liuyao12.github.io/computable-analysis/sect0005.html#sec:pi-scoreboard),
and the blueprint-links column points to the relevant generated blueprint
anchors for each computation.

| Computation | Blueprint links | Description | Definition verified | Equivalent to `piCircleArea` |
| --- | --- | --- | --- | --- |
| `piCircleArea` | [Ch. 2: circle-area algorithm](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:circle-area-stage-algorithm) | Rational midpoint area exhaustion using increment/decrement triangles; current baseline for pi comparisons. | ✓ | N/A |
| `piCircumference` | [Ch. 2: circumference algorithm](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:circle-circumference-stage-algorithm) | Rational polygon circumference using interval square roots for side lengths. | ✗ | ✗ |
| **Arctangent routes** | [Ch. 2: geometric](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:arctan-area-stage-algorithm), [Ch. 3: integral](https://liuyao12.github.io/computable-analysis/ch-integrals.html#def:arctan-integral), [Ch. 4: `arctanSeries`](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#def:arctan-series), [`4 * arctanSeries(1)` to area pi](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:power-series-arctan-area-pi), [`piMachin` agreement](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:leibniz-machin) | This block contains pi routes that first compute arctangent values and then multiply or combine them to get pi: `4 * arctanGeom(1)`, the arctangent integral rows, `4 * arctanSeries(1)`, and `piMachin`.  The Leibniz series is represented only by the endpoint row `4 * arctanSeries(1)`.  `piMachin` belongs here because its first bridge is agreement with `4 * arctanSeries(1)`. |  |  |
| `4 * arctanGeom(1)` | [Ch. 2: geometric arctangent](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:arctan-area-stage-algorithm) | Geometric sector-area arctangent at slope `1`; it has stage equality with `piCircleArea`. | ✓ | ✓ |
| `4 * arctanIntegralRectangleForAtOne` | [Ch. 3: finite rectangle comparison](https://liuyao12.github.io/computable-analysis/ch-integrals.html#thm:finite-arctan-integral-comparison) | Domain-aware `ConstructionFor` packaging of midpoint rectangle sums for `integral_0^1 dt / (1 + t^2)`, using the same rational refinement schedule as `arctanGeom(1)`. | ✓ | ✓ |
| `4 * arctanIntegral(1)` | [Ch. 3: arctangent integral](https://liuyao12.github.io/computable-analysis/ch-integrals.html#def:arctan-integral) | Integral arctangent, `4 * integral_0^1 dt / (1 + t^2)`. | ✗ | ✗ |
| `4 * arctanSeries(1)` | [Ch. 4: arctan series](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#def:arctan-series), [`arctanSeries(1)` endpoint](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:leibniz-arctan), [area comparison target](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:power-series-arctan-area-pi) | Power-series arctangent at `1`; at this endpoint its alternating expansion is the historical Leibniz series. | ✓ | ✗ |
| `piMachin` | [Ch. 4: Machin tangent identity](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:machin-tangent), [`piMachin` to `4 * arctanSeries(1)`](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:leibniz-machin) | Machin's arctangent-series computation, `4 * (4 * arctanSeries(1/5) - arctanSeries(1/239))`; it is grouped with the arctangent routes because its comparison first passes through `4 * arctanSeries(1)`. | ✓ | ✗ |
| `6 * arcsinIntegral(1/2)` | [Ch. 3: inverse elementary integrals](https://liuyao12.github.io/computable-analysis/ch-integrals.html#def:inverse-elementary-integral-identities) | Period formula `pi/6 = integral_0^(1/2) dx / sqrt(1 - x^2)`. | ✗ | ✗ |
| `NewtonSegmentPi` | [Ch. 1: sources of raw reals](https://liuyao12.github.io/computable-analysis/sect0002.html#rem:sources-of-raw-reals) | Newton circle-segment formula `pi/12 + sqrt(3)/8 = integral_0^(1/2) sqrt(1 - x^2) dx`. | ✗ | ✗ |
| `GaussianPi` | [Ch. 1: sources of raw reals](https://liuyao12.github.io/computable-analysis/sect0002.html#rem:sources-of-raw-reals) | Gaussian integral `sqrt(2*pi) = integral_(-infty)^infty exp(-x^2/2) dx`; pi is recovered by squaring and halving. | ✗ | ✗ |
| `baselSeriesRaw` / `pi^2/6` | [Ch. 4: zeta-two intervals](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#def:zeta-two-raw) | Euler's Basel series, `zeta(2) = 1 + 1/4 + 1/9 + ... = pi^2/6`; the zeta-side interval is verified. | ✓ | ✗ |
| `Brouncker(4/pi)` | [Ch. 1: sources of raw reals](https://liuyao12.github.io/computable-analysis/sect0002.html#rem:sources-of-raw-reals) | Continued fraction for `4 / pi`, with finite truncations expected to give rational bounds. | ✗ | ✗ |
| **Logarithm-at-i routes** | [Ch. 5: route overview](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:log-at-i-pi-routes), [series continuation](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#def:complex-log-series-at-i), [path integral](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#def:complex-log-path-integral-at-i), [inverse exp](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#def:complex-log-inv-exp-at-i), [Euler identity](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:euler-identity) | These rows all compute pi from the single formula `pi = -2i * Log(i)`, using different definitions/computations of `Log(i)`.  They are intended tests for branch control, agreement of logarithm constructions, and Euler's identity. |  |  |
| `-2i * LogSeries(i)` | [Ch. 5: series-continuation log](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#def:complex-log-series-at-i), [log-at-`i` route](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:log-at-i-pi-routes), [Euler identity](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:euler-identity) | Complex logarithm obtained from local power-series exponential data and a certified branch taking `i` back to a quarter turn. | ✗ | ✗ |
| `-2i * LogPathIntegral(i)` | [Ch. 5: path-integral log](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#def:complex-log-path-integral-at-i), [log-at-`i` route](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:log-at-i-pi-routes) | Complex logarithm as a path integral of `dz/z` from `1` to `i`. | ✗ | ✗ |
| `-2i * LogInvExp(i)` | [Ch. 5: inverse-exp log](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#def:complex-log-inv-exp-at-i), [log-at-`i` route](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:log-at-i-pi-routes), [Euler identity](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:euler-identity) | Logarithm as the chosen inverse branch of complex exponential, with Euler identity proving the branch value at `i`. | ✗ | ✗ |

The area loop validity package is now formalized as
`PiProofs.AreaLoopValidity.areaValid`, and it transports directly to
`PiProofs.fourArctanGeomOneValid` and
`PiProofs.four_arctanGeom_one_equiv_piCircleArea`.
The geometric arctangent algorithm is also verified on the unit branch as
`ArctanGeometry.arctanGeom_valid_on_unit`, by direct ordered/nested/shrinking
proofs for the increment/decrement loop.  The same validity is packaged on the
power-series domain `|x| <= 1` as
`ArctanGeometry.arctanGeom_valid_on_powerSeriesDomain`, so the kernel-comparison
route no longer needs to assume global validity of the geometric arctangent.
The concrete rectangle-sum arctangent route is also completed through the
domain-aware theorem
`PiProofs.four_arctanIntegralRectangleForAtOne_equiv_piCircleArea`; the more
general older `arctanIntegral(1)` row remains pending because that
point-Riemann construction wrapper has not yet been identified with this
rectangle schedule.  The rectangle schedule itself is now verified more
generally as `ArctanGeometry.arctanIntegralRectangleRaw_valid` and
`IntegralIdentities.arctanIntegralRectangleFor_valid` for rational
`0 <= x <= 1`, and it is now proved equivalent to `arctanGeom x` on that
unit branch.  The same fact is packaged as the function-level agreement
`IntegralIdentities.arctanIntegralRectangleFunctionAgreement`.  The scoreboard
row records the specialization needed for pi.

The baseline self theorem `piCircleArea_equiv_self` exists but is not counted
as an equivalence target.  The series-arctangent-to-area route is now reduced
to `PiProofs.LeibnizEqualsRectangleRawAtOne`: Lean now supplies the
Taylor-kernel rectangle construction, the geometric-kernel comparison, and the
transport between the power-series statement and the concrete comparison of
Leibniz intervals with the rectangle-sum integral at `1`.  The scoreboard
counts the Leibniz alternating series only once, under the explicit name
`4 * arctanSeries(1)`.  Lean also proves the finite arctangent-kernel
bracketing lemmas
`Taylor.ArctanKernel.kernelPartial_odd_le_kernel` and
`Taylor.ArctanKernel.kernel_le_kernelPartial_even`, which are the pointwise
rational inequalities needed for that comparison route.  The older
unit-interval agreement theorem still feeds this pointwise bridge when broader
arctangent comparison data is available.
Lean now also identifies the Leibniz endpoints with the integrated odd/even
finite kernel truncations over `[0,1]` via
`PiProofs.LeibnizValidity.endpoints_eq_kernelPartialIntegral`.  The concrete
remaining finite target has been sharpened to
`PiProofs.LeibnizRectangleBridge.LeibnizRectangleKernelCellBoundsAtOne`:
prove the even/odd finite kernel-truncation inequalities on each cell of the
midpoint partition.  Lean sums those cell inequalities to
`PiProofs.LeibnizRectangleKernelBoundsAtOne`, and the wrapper
`PiProofs.leibnizEqualsRectangleRawAtOne_of_kernelBounds` then gives the
raw-real equivalence needed by the table route.
The preferred mathematical target is now the one-cell version
`PiProofs.LeibnizRectangleBridge.LeibnizRectangleUniformCellBoundsAtOne`: prove
the even lower-cell inequality on every rational unit cell and the odd
upper-cell inequality on every nonnegative ordered rational cell.  Lean proves
`PiProofs.LeibnizRectangleBridge.cellBounds_of_uniformCellBounds` and the
table-facing wrapper
`PiProofs.four_arctanSeries_one_equiv_piCircleArea_of_uniformCellBounds`, so
that uniform one-cell result is sufficient to complete the `4 * arctanSeries(1)`
equivalence row.
Lean now also proves the pointwise finite-division bounds behind this target as
`PiProofs.LeibnizRectangleBridge.leibnizRectanglePointwiseCellBoundsAtOne`.  The
remaining analytic/combinatorial bridge has been isolated as
`PiProofs.LeibnizRectangleBridge.LeibnizRectanglePointwiseIntegralBridgeAtOne`:
turn those pointwise bounds into the corresponding finite polynomial integral
cell bounds.  The wrapper
`PiProofs.four_arctanSeries_one_equiv_piCircleArea_of_pointwiseIntegralBridge`
then completes the table row from that bridge.
The base package
`PiProofs.LeibnizRectangleBridge.leibnizRectangleKernelCellBoundsAtOneBase`
is formalized: the even `m = 0` lower-cell inequality holds on every unit
partition, and the first odd `m = 1` upper-cell inequality is proved on every
nonnegative ordered partition.
As a computational regression check on the full cellwise target, Lean now also
certifies the concrete midpoint partitions through stage `n <= 12` as
`PiProofs.LeibnizRectangleBridge.leibnizRectangleKernelCellBoundsAtOneUpToTwelve`.
The bridge theorems
`PiProofs.LeibnizRectangleBridge.cellBoundsUpTo_of_cellBounds` and
`PiProofs.LeibnizRectangleBridge.cellBounds_of_cellBoundsUpToAll` record that
the full cellwise theorem is exactly the same target as proving every finite
prefix.
For Machin, Lean now proves
`PiProofs.leibnizEqMachin_iff_machinBranchIdentity`: the remaining branch
identity is exactly the remaining raw-real agreement target, after cancelling
the common outer factor `4`.  The bridge from a geometric Machin branch law now
uses `PiProofs.MachinIdentity.PowerSeriesEqualsRectangleKernelAtMachinInputs`
through `PiProofs.leibnizEqMachin_of_powerSeriesRectangleKernelAtMachinInputs`;
this isolates the remaining analytic checks to the power-series/rectangle
kernel equalities at `1/5`, `1/239`, and `1`, plus the geometric branch law.
The table-facing bridge
`PiProofs.piMachin_equiv_piCircleArea_of_powerSeriesRectangleKernelAtMachinInputs`
then connects Machin to the area baseline once those inputs are supplied.

The public `piCircleArea` is the increment/decrement loop.  Polygon-boundary
code that remains in Lean is internal scaffolding for circumference and finite
Archimedes estimates, not another pi computation to count.
For the circumference row, the remaining certification target is now isolated
as `PiProofs.CircumferenceLinearRemainders`: prove dyadic one-step refinement
for `piCircumference` and any explicit linear width bound.  The public area
validity is already reused by
`PiProofs.piProofsComplete_of_circumferenceRemainders`.
Lean now reduces the path-width part of that width-bound target to exact finite
data: each segment interval has the power-of-two square-root bisection width
recorded by `PiProofs.pointSegmentLengthInterval_width_eq`, and a whole
rational polygonal path has width equal to the sum of those segment budgets via
`PiProofs.rationalPointPathLength_width_eq_segmentBudget`.  The public
circumference width is also reduced to the quarter-gap target by
`PiProofs.piCircumference_compute_width_eq`; it is enough to prove
`PiProofs.CircumferenceQuarterGapLinearBound`, i.e. an explicit linear bound
on twice the gap between the outer path upper endpoint and the inner path lower
endpoint.  The outer tangent fan is now certified to lie inside the outer path
interval by `PiProofs.outerFanPerimeter_mem_outerQuarterLength`.  Lean further
reduces the quarter-gap bound to
`PiProofs.CircumferenceFanGapPathBudgetLinearBound`: the quarter gap is bounded
by the rational outer-minus-inner fan perimeter gap plus the two path-width
budgets, via
`PiProofs.circumferenceQuarterGap_le_fanGap_add_pathWidthBudget`.  The combined
linear target now splits into independent fan-gap and path-budget linear
bounds by `PiProofs.fanGapPathBudgetLinearBound_of_parts`; the path-budget side
has the segment-count reduction
`PiProofs.circumferencePathWidthBudget_le_three_stage_mul` and is now reduced
to explicit adjacent inner-chord and outer-tangent formulas by
`PiProofs.circumferencePathWidthBudgetLinearBound_of_formulaSegmentUniformLinearBound`.
The tangent entry and exit cross terms are now both identified with the same
rational expression `(v - u) / (1 + u * v)`, and Lean records positivity for
the chord and tangent formulas.
The remaining finite rational predicate is
`PiProofs.CircumferenceFormulaSegmentUniformLinearBound`.

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
