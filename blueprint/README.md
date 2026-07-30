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
- Generate each frame from exact finite rational state.  The GIF illustrates
  the computation; a linked Lean declaration establishes any certificate.
- Choose a static print frame that still displays the construction, rather
  than merely the last, nearly converged state.

| Animation | Exact finite state shown | Source |
| --- | --- | --- |
| Rational-circle subdivision | The `Stage` points for (1,2,4,8) equal parameter cells, their projections, and the inscribed/circumscribed polygon bounds | `scripts/generate_rational_circle_animation.py` |
| Arctangent rectangle enclosure | The lower/right and upper/left endpoint rectangles for (1/(1+t^2)) on the midpoint partitions with (1,2,4,8) cells | `scripts/generate_arctan_rectangle_animation.py` |
| Square-root secant--tangent | The rational secant and tangent intersections defining four successive brackets for `sqrt(2)` | `scripts/generate_sqrt_secant_tangent_animation.py` |
| Integration-by-parts product cell | Three exact rational `((u_i,v_i),(u_{i+1},v_{i+1}))` states whose two strips tile the endpoint-product increment | `scripts/generate_integration_by_parts_animation.py` |
| Single-turn integral | Rational secant--tangent brackets for `sqrt(2)`, the monotone tails of `4-(t^2-2)^2`, and the exact middle box `(r-l)[0,4]` | `scripts/generate_single_turn_integral_animation.py` |
| FTC endpoint comparison | Dyadic lower/right and upper/left derivative rectangles for `F(t)=t^2` and `F'(t)=2t`, beside the exact endpoint rise | `scripts/generate_ftc_endpoint_animation.py` |

Good candidates are finite product-rectangle reindexing, a piecewise-monotone
split around a rational turning bracket, finite FTC endpoint comparison, and
Peano--Baker partial sums.  Add one only alongside its precise finite evaluator
and its checked bounds, never as an illustration of an unimplemented
completed-real argument.
