# Fundamental Matrix

A standalone classical essay at `fundamental-matrix.html`, hosted by the
Computable Analysis project and linked from its home, contents and Differential
Equations chapter. The page itself has no project branding or formalization
status discussion.

## Pedagogical progression

The exposition stays with second-order equations. It starts by integrating
acceleration twice, including the initial position and velocity, and works out
successive approximations explicitly before introducing matrix notation:

1. `y'' = -y`: integrations produce cosine and sine; two initial motions give
   two reusable solutions.
2. `y'' = y^2`: a nonlinear comparison with the first three complete polynomial
   iterates and a local convergence argument. Existing coefficients change;
   Picard iteration is not generally Taylor truncation.
3. `y'' = ty`: the same integrations construct two normalized Airy solutions.
4. `y'' + p(t)y' + q(t)y = 0`: place the two solutions and their velocities in
   a 2-by-2 fundamental matrix, then derive its Picard/Peano–Baker iteration.
5. Add forcing in the same iteration. Derive the unit-velocity response kernel,
   check the forcing formula, and work out the constant and resonant oscillator
   responses and `y'' = ty + 1`.
6. Explain factorial convergence and uniqueness, with optional proof details.

The twice-integrated scalar iteration and the first-order state-vector
iteration are explicitly distinguished: they have the same solution but need
not have identical finite-stage numbering. For the general damped equation,
the kernel includes the Wronskian denominator.

## Presentation and build

The published page is a single reading column. There are no plots, sliders,
model selectors, scroll-following, numerical dashboards, or runtime scripts.
The essential calculations are always visible. Native HTML disclosures contain
only supplementary proofs. All text and equations work with JavaScript disabled.

`index.template.html` contains the complete exposition in authored LaTeX.
`style.css` controls the static page. `build.cjs` compiles the equations to native
MathML with the existing pinned build dependency, mathjax-full 3.2.1, and inlines
the CSS. No font files are copied.

The older notebook sources (`app.js`, `engine.js`, `nonlinear.js`, `nonlinear.html`,
`site.css`, and `site.js`) are retained as unshipped development history; they
are not included by the essay builder or the publication integration. The
exact polynomial engine is still used by the build-time algebra tests.

```sh
npm install --prefix book/fundamental-matrix --ignore-scripts --no-audit --no-fund
node book/fundamental-matrix/test-second-order.cjs
python .github/reader-edition/fundamental_matrix.py --site site --revision REVISION
python .github/reader-edition/test_fundamental_matrix.py --site site --report reader-edition-tests
```

`test-second-order.cjs` checks the monomial integration rule, oscillator and
Airy iterates, all coefficients of the nonlinear third iterate, the nonlinear
contraction constant, forced examples, and the different scalar/matrix stage
numbering using exact rational arithmetic. These are finite regression tests,
not a formalization of the analytic convergence theorems.

The publication tests check incoming links, original-byte preservation outside
delimited additions, idempotent integration, mathematical typesetting, five
viewport widths, ordinary anchor navigation, proof disclosures, and operation
with JavaScript disabled. Screenshots and reports are retained in the existing
reader-edition-validation artifact.

The existing verified publication workflow and all Lean sources remain
unchanged. The metadata keeps the documentation revision separate from the
previously verified proof-source snapshot; no new Lean theorem is claimed.
