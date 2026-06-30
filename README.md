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

Current count: definitions completed `5/14`; equivalences to `piCircleArea`
formalized `1/13` applicable rows.  The baseline row `piCircleArea` is `N/A`
for equivalence scorekeeping.

| Computation | Blueprint | Description | Definition verified | Equivalent to `piCircleArea` |
| --- | --- | --- | --- | --- |
| [`piCircleArea`](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:circle-area-stage-algorithm) | Chapter 2 | Rational midpoint area exhaustion using increment/decrement triangles; current baseline for pi comparisons. | ✓ | N/A |
| [`piCircumference`](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:circle-circumference-stage-algorithm) | Chapter 2 | Rational polygon circumference using interval square roots for side lengths. | ✗ | ✗ |
| **Arctangent routes** | [Chapters 2-4](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#def:arctan-series) | These rows compute pi through geometric, integral, or series arctangent algorithms. |  |  |
| [`4 * arctanGeom(1)`](https://liuyao12.github.io/computable-analysis/ch-rational-circle-trigonometry.html#def:arctan-area-stage-algorithm) | Chapter 2 | Geometric sector-area arctangent at slope `1`; it has stage equality with `piCircleArea`. | ✓ | ✓ |
| [`4 * arctanIntegral(1)`](https://liuyao12.github.io/computable-analysis/ch-integrals.html#def:arctan-integral) | Chapter 3 | Integral arctangent, `4 * integral_0^1 dt / (1 + t^2)`. | ✗ | ✗ |
| [`4 * arctanSeries(1)`](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#def:arctan-series) | Chapter 4 | Power-series arctangent at `1`, i.e. the Leibniz alternating series written as an arctangent computation. | ✓ | ✗ |
| [`piMachin`](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#thm:machin-tangent) | Chapter 4 | Machin's arctangent combination, `4 * (4 * arctanSeries(1/5) - arctanSeries(1/239))`. | ✓ | ✗ |
| [`6 * arcsinIntegral(1/2)`](https://liuyao12.github.io/computable-analysis/ch-integrals.html#def:inverse-elementary-integral-identities) | Chapter 3 | Period formula `pi/6 = integral_0^(1/2) dx / sqrt(1 - x^2)`. | ✗ | ✗ |
| [`NewtonSegmentPi`](https://liuyao12.github.io/computable-analysis/sect0002.html#rem:sources-of-raw-reals) | Chapter 1 | Newton circle-segment formula `pi/12 + sqrt(3)/8 = integral_0^(1/2) sqrt(1 - x^2) dx`. | ✗ | ✗ |
| [`GaussianPi`](https://liuyao12.github.io/computable-analysis/sect0002.html#rem:sources-of-raw-reals) | Chapter 1 | Gaussian integral `sqrt(2*pi) = integral_(-infty)^infty exp(-x^2/2) dx`; pi is recovered by squaring and halving. | ✗ | ✗ |
| [`baselSeriesRaw` / `pi^2/6`](https://liuyao12.github.io/computable-analysis/ch-infinite-series.html#def:zeta-two-raw) | Chapter 4 | Euler's Basel series, `zeta(2) = 1 + 1/4 + 1/9 + ... = pi^2/6`; the zeta-side interval is verified. | ✓ | ✗ |
| [`Brouncker(4/pi)`](https://liuyao12.github.io/computable-analysis/sect0002.html#rem:sources-of-raw-reals) | Chapter 1 | Continued fraction for `4 / pi`, with finite truncations expected to give rational bounds. | ✗ | ✗ |
| **Logarithm-at-i routes** | [Chapter 5](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:euler-identity) | These rows compute pi from `Log(i) = i*pi/2`; Euler identity is an essential bridge. |  |  |
| [`-2i * LogSeries(i)`](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#def:exp-representations) | Chapter 5 | Complex logarithm obtained from power-series exponential data and branch inversion near `i`. | ✗ | ✗ |
| [`-2i * LogIntegral(i)`](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#def:logarithm-integral) | Chapter 5 | Complex logarithm as a path integral of `dz/z` from `1` to `i`. | ✗ | ✗ |
| [`-2i * LogInvExp(i)`](https://liuyao12.github.io/computable-analysis/ch-exponential-logarithm.html#thm:euler-identity) | Chapter 5 | Logarithm as the chosen inverse branch of complex exponential, with Euler identity locating `i`. | ✗ | ✗ |

The area loop validity package is now formalized as
`PiProofs.AreaLoopValidity.areaValid`, and it transports directly to
`PiProofs.fourArctanGeomOneValid` and
`PiProofs.four_arctanGeom_one_equiv_piCircleArea`.

The baseline self theorem `piCircleArea_equiv_self` exists but is not counted
as an equivalence target.  The series-arctangent-to-area route is now reduced
to `PowerSeriesAgreesOnUnit`, and the scoreboard counts that computation only
once as `4 * arctanSeries(1)`.

The public `piCircleArea` is the increment/decrement loop.  Polygon-boundary
code that remains in Lean is internal scaffolding for circumference and finite
Archimedes estimates, not another pi computation to count.

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
