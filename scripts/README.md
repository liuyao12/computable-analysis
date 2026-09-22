# Animation conventions

The Python generators in this directory are reproducible sources for the GIF
and PNG figures in `blueprint/src/assets`.

For a Cartesian plot, use one screen length per mathematical unit on both
axes: a `0.5 × 0.5` grid cell must render as a square.  This applies to the
rational-integral, arctangent, secant--tangent, circle, and
integration-by-parts figures.

For a graph written with a normalized trigonometric input such as
`sin(pi*t)` or `sin(pi*t)/(pi*t)`, map one `t`-unit to `pi` screen value-units.
Equivalently, give the horizontal coordinate the scale it would have after
the substitution `theta = pi*t`.  This preserves the familiar visual form of
`sin(theta)` and `cos(theta)` instead of incorrectly treating the normalized
parameter as radians.

Diagrams that are not coordinate plots, such as the Peano--Baker word tiles,
do not have an axis-aspect requirement.  After changing a generator, rerun it
to update both its GIF and its static PNG fallback, then visually inspect the
PNG before publishing.

# Leibniz benchmark

```sh
lake build ComputableAnalysis.LeibnizPiTaylor
lake env lean scripts/check_leibniz.lean
```

The focused check verifies all-stage theorem signatures, rejects unfinished
proof dependencies, prints inherited axioms, and checks that the computational
and FTC proofs use different comparison certificates. Full project-declaration
closures are written to `tmp/leibniz-dependency-closure.txt`. See
`docs/LEIBNIZ_PI.md` for the whole-library and blueprint verification commands.
