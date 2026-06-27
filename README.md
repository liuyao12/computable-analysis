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

Current count: definitions completed `3/7`; equivalences to `piCircleArea`
formalized `3/7`, including the baseline row.

| Computation | Description | Definition verified | Equivalent to `piCircleArea` |
| --- | --- | --- | --- |
| `piCircleArea` | Rational midpoint area exhaustion using increment/decrement triangles; current baseline for pi comparisons. | ✗ | ✓ |
| `piCircumference` | Rational polygon circumference using interval square roots for side lengths. | ✗ | ✓ |
| `piLeibniz` | Alternating Leibniz series, `4 * (1 - 1/3 + 1/5 - ...)`. | ✓ | ✗ |
| `piMachin` | Machin formula, `4 * (4 * arctan(1/5) - arctan(1/239))`. | ✓ | ✗ |
| `4 * arctan(1)` | Power-series arctangent at `1`, equal to the Leibniz computation. | ✓ | ✗ |
| `4 * arctanGeom(1)` | Geometric sector-area arctangent at slope `1`. | ✗ | ✓ |
| `4 * arctanIntegral(1)` | Integral arctangent, `4 * integral_0^1 dt / (1 + t^2)`. | ✗ | ✗ |

The first open geometric target is the midpoint-loop validity package:
`PiCircleAreaLoopOrdered`, `PiCircleAreaLoopNested`, and
`PiCircleAreaLoopWidthsShrink`.

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
