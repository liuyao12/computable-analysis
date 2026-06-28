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

Current count: definitions completed `6/13`; equivalences to `piCircleArea`
formalized `1/12` applicable rows.  The baseline row `piCircleArea` is `N/A`
for equivalence scorekeeping.

| Computation | Description | Definition verified | Equivalent to `piCircleArea` |
| --- | --- | --- | --- |
| `piCircleArea` | Rational midpoint area exhaustion using increment/decrement triangles; current baseline for pi comparisons. | ✓ | N/A |
| `piCircumference` | Rational polygon circumference using interval square roots for side lengths. | ✗ | ✗ |
| **Arctangent-at-one routes** | The following rows compute pi through `4 * arctan(1)` using geometric, integral, or series representations. |  |  |
| `4 * arctanGeom(1)` | Geometric sector-area arctangent at slope `1`; it has stage equality with `piCircleArea`. | ✓ | ✓ |
| `4 * arctanIntegral(1)` | Integral arctangent, `4 * integral_0^1 dt / (1 + t^2)`. | ✗ | ✗ |
| `4 * arctan(1)` | Power-series arctangent at `1`, equal to the Leibniz computation. | ✓ | ✗ |
| `piLeibniz` | Alternating series for `4 * arctan(1)`, namely `4 * (1 - 1/3 + 1/5 - ...)`. | ✓ | ✗ |
| `6 * arcsinIntegral(1/2)` | Period formula `pi/6 = integral_0^(1/2) dx / sqrt(1 - x^2)`. | ✗ | ✗ |
| `NewtonSegmentPi` | Newton circle-segment formula `pi/12 + sqrt(3)/8 = integral_0^(1/2) sqrt(1 - x^2) dx`. | ✗ | ✗ |
| `GaussianPi` | Gaussian integral `sqrt(2*pi) = integral_(-infty)^infty exp(-x^2/2) dx`; pi is recovered by squaring and halving. | ✗ | ✗ |
| `piMachin` | Machin formula, `4 * (4 * arctan(1/5) - arctan(1/239))`. | ✓ | ✗ |
| `baselSeriesRaw` / `pi^2/6` | Euler's Basel series, `zeta(2) = 1 + 1/4 + 1/9 + ... = pi^2/6`; the zeta-side interval is verified. | ✓ | ✗ |
| `Brouncker(4/pi)` | Continued fraction for `4 / pi`, with finite truncations expected to give rational bounds. | ✗ | ✗ |
| `ComplexLogPi` | One chosen complex-log pi formula, for example principal-branch `log(-1) = i*pi`, with three computable `Log` constructions compared; Euler identity is a bridge theorem, not a separate pi computation. | ✗ | ✗ |

The area loop validity package is now formalized as
`PiProofs.AreaLoopValidity.areaValid`, and it transports directly to
`PiProofs.fourArctanGeomOneValid` and
`PiProofs.four_arctanGeom_one_equiv_piCircleArea`.  The first open
geometric bridge is `PiCircleAreaPolygonAgreement`.

The baseline self theorem `piCircleArea_equiv_self` exists but is not counted
as an equivalence target.  The Leibniz-to-area route is now reduced to
`PowerSeriesAgreesOnUnit` via
`piLeibniz_equiv_piCircleArea_of_powerSeriesGeometryAgreement`.

The public `piCircleArea` is now the increment/decrement loop.  The older
polygon-boundary presentation is retained as `piCircleAreaPolygon` only as
proof scaffolding.  The loop is now directly verified; the next proof step is
`PiCircleAreaPolygonAgreement` so the polygon-based Archimedes, circumference,
and polygon-scaffold comparisons transport back to the public baseline.

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
