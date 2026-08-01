# Computable Analysis Blueprint

This directory is a Lean blueprint for the `ComputableAnalysis` package.
It records the mathematical plan in LaTeX and attaches Lean declaration names
where the project already has definitions or theorem statements.

From the repository root:

```bash
python -m pip install -r blueprint/requirements.txt
leanblueprint pdf
leanblueprint web
```

When the Lean environment is available, use the declaration check as a sanity
pass:

```bash
leanblueprint checkdecls
```

The source files are in `blueprint/src`.  The two entry points are
`blueprint/src/print.tex` and `blueprint/src/web.tex`; both include
`blueprint/src/content.tex`, which then includes the numbered chapter files.

## Animated finite stages

The web blueprint may use a looping GIF when a picture can show a literal
finite rational state more clearly than a paragraph.  Print uses a carefully
chosen static PNG frame.  The pseudocode specifies the update; an animation
never supplies theorem status, which still comes from linked Lean declarations.

Use the following convention for every new algorithm animation:

- Put the precise update immediately beside it in Python-like pseudocode;
  rationals are implicit unless a special representation is needed.
- Make the GIF almost wordless: use only the mathematical variables, axes,
  and colour needed to follow one finite update—no title, legend, or prose.
- Do not repeat in prose what the GIF and its pseudocode already show; retain
  only the invariant or certificate scope that the picture cannot establish.
- Generate every computational mark in a frame from exact finite rational
  state.  If a smooth curve is retained as a visual reference, make the
  rational value brackets visible and say that the curve is not an evaluator.
  The GIF illustrates the computation; a linked Lean declaration establishes
  any certificate.
- Use equal horizontal and vertical unit scales for Cartesian geometry and
  ordinary function plots.  For a normalized trigonometric input such as
  `sin(pi*t)`, map one `t`-unit to its angle `pi` so the graph has the aspect
  of `sin(theta)`, not of a sine function whose argument is measured in
  radians incorrectly.
- Choose a static print frame that still displays the construction, rather
  than merely the last, nearly converged state.

| Animation | Exact finite state shown | Source |
| --- | --- | --- |
| Rational-circle subdivision | The `Stage` points for (1,2,4,8) equal parameter cells, their projections, and the inscribed/circumscribed polygon bounds | `scripts/generate_rational_circle_animation.py` |
| Arctangent rectangle enclosure | The lower/right and upper/left endpoint rectangles for (1/(1+t^2)) on the midpoint partitions with (1,2,4,8) cells | `scripts/generate_arctan_rectangle_animation.py` |
| Exact rational monotone stage | The lower/right and upper/left endpoint rectangles for the decreasing rational function (1/(1+t^2)) | `scripts/generate_monotone_integral_animation.py` |
| Interval-valued sine stage | Rational alternating-series boxes with a retained halving error radius at the dyadic inputs of sin(pi*t); lower-left and upper-right Darboux rectangles use those same endpoints | `scripts/generate_interval_sine_integral_animation.py` |
| Square-root secant--tangent | The rational secant and tangent intersections defining four successive brackets for `sqrt(2)` | `scripts/generate_sqrt_secant_tangent_animation.py` |
| Substitution partition | Equal rational divisions of a fixed `t0`--`t1` parameter interval and their unequal exact images under `x=phi(t)` | `scripts/generate_substitution_partition_animation.py` |
| Integration-by-parts paired partition | One equal `t0`--`t1` parameter mesh, equal `f(t_i)` steps, unequal `g(t_i)` steps, and the horizontal-first/vertical-first zigzags through the same samples | `scripts/generate_integration_by_parts_animation.py` |
| Turning-bracket integral illustration | A normalized-sinc local minimum with a shrinking rational bracket, two monotone tails, and a bounded middle gap | `scripts/generate_single_turn_integral_animation.py` |
| FTC endpoint comparison | Dyadic lower/right and upper/left derivative rectangles for `F(t)=t^2` and `F'(t)=2t`, beside the exact endpoint rise | `scripts/generate_ftc_endpoint_animation.py` |
| Peano--Baker words | The exact `orderedIndexWords` recursion for 0, 1, 2, and 3 samples, preserving newest-to-oldest matrix-factor order | `scripts/generate_peano_baker_words_animation.py` |

Further animations should be added only alongside their precise finite
evaluator and checked bounds, never as illustrations of an unimplemented
completed-real argument.
