# Fundamental Matrix

A standalone, classical exposition hosted at `fundamental-matrix.html` within
the Computable Analysis site. The book home page, contents and Differential
Equations chapter link into it. The page itself contains no project branding,
book menu, foundational prerequisites or formalization-status discussion.

Picard iteration is the starting point. Two nonlinear examples come before the
matrix construction:

- `y' = y^2`, `y(0) = 1`: exact polynomial iterates, coefficient stabilization,
  uniform convergence before the singularity, and finite-time blow-up.
- `y' = 1-y^2`, `y(0) = 0`: exact polynomial iterates converging to tanh, with
  increasing even and decreasing odd iterates bracketing the answer on [0,1].

The text distinguishes Picard polynomials from Taylor truncations and explains
why nonlinear solution maps do not generally give a reusable fundamental
matrix. It then retains the normalized matrix, forcing integral, higher-order
reduction, factorial convergence estimate and four linear worked examples.

The interactive notebook follows the text on desktop and sits in document flow
on mobile. Linear examples reuse cached augmented matrix terms. Nonlinear
examples have fixed initial data and no matrix display; their degree grows as
2^N-1, so the slider stops at seven iterations instead of 36. The two nonlinear
uniform bounds are explained in the text: the increasing endpoint error for
quadratic growth, and the gap between adjacent bounding iterates for saturation.

## Source and build

`index.template.html` contains the main LaTeX exposition and an include marker
for `nonlinear.html`. `build.cjs` compiles their equations to native MathML and
inlines `style.css`, `engine.js`, `nonlinear.js`, and `app.js`. `site.css` and
`site.js` measure the standalone navigation height without adding a book shell.

`engine.js` is the unchanged exact rational linear matrix engine.
`nonlinear.js` extends the same notebook interface with polynomial squaring and
integration; it does not approximate nonlinear equations with a fixed matrix.
All polynomial coefficients and error bounds use reduced BigInt rationals.
Floating point is used for drawing and decimal display only. Mathematical
bounds do not include those rendering errors.

The build-only dependency remains mathjax-full 3.2.1. The resulting page needs
no external runtime assets and includes no font files.

```sh
npm install --prefix book/fundamental-matrix --ignore-scripts --no-audit --no-fund
npm test --prefix book/fundamental-matrix
python .github/reader-edition/fundamental_matrix.py --site site --revision REVISION
python .github/reader-edition/test_fundamental_matrix.py --site site --report reader-edition-tests
```

`test.cjs` checks the unchanged linear engine. `test-nonlinear.cjs` checks exact
polynomial recurrences, displayed coefficients, initial values, coefficient
stabilization, and separately labelled sampled reference/error consistency.
Browser checks cover all seven examples, nonlinear iteration limits, hidden
matrix/initial-state controls, scroll-following, native MathML, no project
branding, incoming book links, and four viewport widths.

Publication still runs through the existing verified reader workflow. Existing
reader changes are delimited incoming links; stripping those additions recovers
the original bytes. Proof data and Lean sources are unchanged. The publication
manifest records the documentation revision separately from the existing proof
source; no additional formalized theorem is claimed.
