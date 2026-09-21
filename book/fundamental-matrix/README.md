# Fundamental Matrix

An interactive reader page in **Computable Analysis**, published at
`fundamental-matrix.html` alongside the existing chapters. It is linked from
book navigation, the home page, and Chapter 14 (Differential equations), with
return links and a keyboard-accessible book contents menu.

The narrative starts with Picard iteration and derives the normalized
fundamental matrix, the forcing integral, higher-order reduction, and a
factorial convergence estimate. Worked examples cover a forced scalar equation
with variable coefficient, the oscillator and resonance, a noncommuting
triangular system with a terminating series, and Airy's equation with forcing.

The right-hand notebook follows the text on desktop and sits in document flow
on mobile. It reuses cached augmented matrix terms when the initial state or
forcing amplitude changes. Coefficients, integrals and tail estimates use
reduced BigInt rationals. Floating-point conversion is limited to rendering and
decimal display. The rational bounds cover series truncation, not drawing error.

## Source and build

- `index.template.html`: mathematical text and authored LaTeX.
- `engine.js`: exact rational polynomial matrix engine, also usable in Node.
- `app.js`: notebook controls, SVG plotting and scroll-following examples.
- `style.css`: original two-column exposition layout.
- `site.css`, `site.js`: book identity, contents menu and measured header height.
- `build.cjs`: compile LaTeX to native MathML and inline the notebook assets.
- `test.cjs`: exact algebraic regressions and separately labelled sampled checks.

The only build dependency is pinned to `mathjax-full` 3.2.1. The generated page
has no external runtime dependencies and includes no font files.

```sh
npm install --prefix book/fundamental-matrix --ignore-scripts --no-audit --no-fund
node book/fundamental-matrix/test.cjs
python .github/reader-edition/fundamental_matrix.py --site site --revision REVISION
python .github/reader-edition/test_fundamental_matrix.py --site site --report reader-edition-tests
```

The integration step runs after the existing checked reader stages in
`.github/workflows/publish_verified_blueprint.yml`. It records the documentation
revision separately from the verified proof-source commit. Existing reader
files receive only delimited navigation or introductory links. Removing those
additions recovers their original bytes; all pre-existing proof data, reference
files and assets remain byte-identical. A preservation manifest is published at
`reading/fundamental-matrix-edition.json`.

Tests cover the exact matrix recurrence, initial values, agreement with direct
Picard iteration, terminating and forced examples, outward error display, all
local links, MathML, keyboard contents navigation, scroll-following, and desktop
and mobile rendering. Sampled comparisons with independent reference functions
are consistency tests, not proofs of uniform bounds.

This is an expository page and executable illustration. It adds no Lean theorem,
proof-map badge, or claim that the general fundamental-matrix theorem has been
formalized in the project. No Lean source or existing proof claim is changed.
