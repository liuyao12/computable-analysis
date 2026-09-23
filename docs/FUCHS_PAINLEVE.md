# Fuchs–Painlevé algebraic differential equations

This is an independent subproject of Computable Analysis, alongside the PDE
work. Import `ComputableAnalysis.AlgebraicODE`. It uses this repository's
`Rat`, `QComplex`, `ComplexRaw`, overlap equivalence, and two-sided rational
finite-difference certificates. There is no Mathlib dependency or Mathlib real.

## Checked forward Fuchs growth theorem

`LinearGrowth` proves a solution-behavior theorem without completing the
rationals. `LinearSolution A R` gives valid component interval algorithms at
rational `0<t≤R`. On each rational `[a,b]⊆(0,R]`, it supplies a positive
rational step radius and a step-dependent output precision such that all
samples `v,w` from sufficiently refined endpoint boxes satisfy

\[
 \|w-v-hA(x)v\|_1\le\varepsilon |h|.
\]

This is the uniform effective local ODE condition. **No growth estimate is a
field of the solution.** The precision depends on `h`, so non-singleton
interval outputs are allowed. `LinearSolution.constant` constructs an actual
solution from any valid raw constant with a supplied width schedule; the
regression uses the nonterminating Bessel-factor evaluator at `1/8`.

If every column of the rational matrix satisfies
`t Σᵢ|Aᵢⱼ(t)|≤N`, then `LinearSolution.fuchs_growth` proves

\[
 \|Y(a)\|_1\le \frac{b^N M}{a^N},\qquad 0<a\le b\le R,
\]

from an outer norm bound `M`. `moderate_growth` obtains `M` by computing
stage-zero boxes at `b`, so every solution has such a bound. Formally,
`NormBound V M` means that every stage box meets the closed rational norm
ball of radius `M`, tested by its nearest-to-zero vector. It does not demand
that the entire coarse box fit in that ball. For singleton computations,
`normBound_exact` proves this is precisely the ordinary rational norm bound.

The proof uses a finite inward mesh and the polynomial inequality
`s^N(t+N(t-s))≤t^(N+1)` for `0≤s≤t`. An arbitrary rational error budget is
removed by rational order reasoning. There is no completed real line,
limit object, exponential, logarithm, integral, compactness, or complex
analytic library in this argument.

For complex rational polynomials `p,q`, `Fuchs.Growth` treats

\[
 z^2 y''+zp(z)y'+q(z)y=0,\qquad Y=(y,zy'),\qquad
 \frac{dY}{dt}=\frac1t
 \begin{pmatrix}0&1\\-q(td)&1-p(td)\end{pmatrix}Y
\]

along `z=td` for a fixed nonzero rational complex direction `d`.
`companion_apply` verifies the real-coordinate matrix identity.
`polynomial_eval_bound` supplies the coefficient estimate, and
`fuchs_ray_moderate` proves polynomial growth for every solution of this
scaled-jet differential system. Its natural exponent is computed by a
rational ceiling of `2+P(R|d|₁)+Q(R|d|₁)`, where `P,Q` are the Horner
absolute-coefficient bounds. The conservative exponent need not be sharp.
`reciprocalSolution` constructs `y=1/t`, `ty'=-1/t`, for `p=2,q=0` using the
existing reciprocal finite-difference theorem; `reciprocal_moderate` applies
the general theorem to obtain `‖Y(a)‖₁≤4/a⁴` for `0<a≤1`.

This is the **forward implication on rational rays for polynomial regular
coefficients**, not the full equivalence usually called Fuchs's criterion.
The solution interface certifies the scaled first-order differential system
directly. A general translation from an independently packaged holomorphic
second-order solution is not yet formalized. Neither arbitrary holomorphic
coefficient germs, uniform sector bounds, a fundamental solution basis, nor
the converse from moderate growth to pole-order bounds is claimed. The
forward theorem is independent of the Frobenius coefficient construction.
A classical comparison is Schnell's [D-modules notes, Lecture 20,
Theorem 20.4](https://www.math.stonybrook.edu/~cschnell/pdf/notes/d-modules.pdf).

## Checked Painlevé I local pole charts

The next nonlinear milestone concerns movable singularities. In the
[DLMF definition](https://dlmf.nist.gov/32.2), the Painlevé property excludes
movable branch points. Constructing pole charts is a local step toward this
property; it does not prove that they exhaust the singularities of arbitrary
solutions.

Put `s=x-p` and seek `y=s⁻² Σ cₙsⁿ` in `y''=6y²+x`. The independently
defined differential residual forces the leading coefficient to be one and
then gives

\[
 c_1=c_2=c_3=0,\quad c_4=-p/10,\quad c_5=-1/6,\quad c_6=q,
 \qquad
 (n-6)(n+1)c_n=6\sum_{k=1}^{n-1}c_kc_{n-k}\quad(n\ge7).
\]

The resonance at `n=6` leaves `q` free. For the more general forcing
`y''=6y²+f(s)`, the same coefficient calculation requires `f₂=0`.
`Tests.quadratic_forcing_obstruction` rejects `f(s)=s²`; thus compatibility
is a proved constraint, not an assumption hidden in the solver.

`Painleve.Laurent.coeff_isSolution` and `solution_unique` prove existence
and uniqueness of the formal Laurent coefficients for supplied rational
`p,q`. With `R=1+6|p|+6|q|`, `coeff_growth` proves `|cₙ|≤Rⁿ`. The proof
controls the nonlinear convolution and divides only by the positive
recurrence denominator at `n≥7`.

For the analytic computation, put `ρ=1/(64R)`, `s=ρt`, and
`U(t)=Σ cₙρⁿtⁿ`. On rational `|t|≤1`, `Painleve.Pole` computes valid raw
interval algorithms for `U`, `U'`, and `U''`. Each has stage width `4/2ⁿ`.
These are actual derivative certificates: for each positive rational `ε`,
nonzero step `h` with `|h|≤ε/8`, and endpoints in `[-1,1]`, a computed
stage depending on `ε,h` makes **every** selection of endpoint samples
`v,w` and derivative sample `d` satisfy

\[
 |w-v-hd|\le\varepsilon|h|.
\]

The reusable `GeometricSeriesCalculus.geometricRaw_hasBoxDerivative`
(in namespace `FormalPowerSeries`) proves this from
`|aₙ|≤M(1/8)ⁿ`, with step radius `ε/(4(M+1))`.
`CauchyProductEstimate.cauchy_prefix_error` bounds the difference between
a product of finite prefixes and its triangular convolution by `M²/2ᴺ`.
Both proofs use finite sums and rational bounds; neither introduces a
completed real type or interchanges unspecified infinite limits.

For **arbitrary samples** `u,v,w` from the three actual stage-`n` boxes,
`Painleve.Pole.equation_error` proves

\[
 \left|t^2w-4tv+6u-6u^2-p\rho^4t^4-\rho^5t^5\right|
 \le146\,2^{-n}.
\]

`equation` supplies the precision stage for any requested rational error.
This is the regularized nonlinear PI equation with certified derivatives,
not just a formal coefficient identity. The independently reconstructed
value `Y=U/(ρt)²` has valid boxes, and `double_pole_bounds` proves at every
stage `n≥2`, for `0<|t|≤1`,

\[
 \frac12\le (\rho t)^2\operatorname{lo}(Y_n)
 \le (\rho t)^2\operatorname{hi}(Y_n)\le\frac32.
\]

Thus the local computation has a genuine double pole at the freely supplied
rational position `p`. The expansion starts
`y=s⁻²-(p/10)s²-(1/6)s³+q s⁴+…`.
`original_equation_identity` checks the exact algebraic change of jet
coordinates back to `y''=6y²+x`.

**Scope:** derivative certificates are for the regular factor in the scaled
rational coordinate. Transporting them to the reconstructed `Y` via the
singular coordinate change is still an analytic adapter obligation; the jet
identity alone is not that proof. Complex-domain charts, arbitrary computable
parameters, continuation from arbitrary initial data, uniqueness among
analytic solutions, and exclusion of every other movable singularity remain
open. These PI charts are not asserted to be algebraic solutions. No global
Painlevé property or algebraic-solution classification is claimed. The
importance of convergence and exhaustion beyond a formal Laurent test is
explained in [Joshi and Halburd's notes](https://www.homepages.ucl.ac.uk/~ucahrha/Publications/Pond-97.pdf).

## Checked first milestone

The convention is the one in [DLMF §32.2](https://dlmf.nist.gov/32.2):

\[
\mathrm{P_I}: y''=6y^2+x,\qquad
\mathrm{P_{II}}(\alpha): y''=2y^3+xy+\alpha.
\]

| Result | Lean declaration | Scope |
|---|---|---|
| Polynomial residual evaluation preserves validity and represented equality | `Expr.evalRaw_valid`, `Expr.evalRaw_equiv` | Arbitrary valid computable complex inputs |
| Exact rational evaluation agrees with the actual raw runtime | `Expr.evalRaw_ofRat` | Equality of raw algorithms, including every stage |
| Euler–Fuchs polynomial coefficient classification | `Fuchs.polynomial_classification` | For `xy'=r y`, every nonzero coefficient has degree `r` |
| Coefficient certificate implies the evaluated differential identity | `Fuchs.polynomial_equation` | Uses the existing executable polynomial derivative |
| Nonzero polynomial solution implies `r` is a natural number | `Fuchs.exponent_of_nonzero_polynomial` | Polynomial solutions only, not all algebraic branches |
| Radical tangent elimination | `Fuchs.radical_euler` | Given `y^n=x^m`, its differentiated identity, `y≠0`, and `n≠0`, derives `nxy'=my` |
| PI has no constant solution | `Painleve.first_no_constant` | Rational constants |
| PII has only the zero affine solution, at `α=0` | `Painleve.affine_classification` | All rational affine candidates |
| PII simple-pole classification | `Painleve.simple_pole_classification` | `y=c/x` solves the equation on the punctured rational line iff `α=-c` and `c∈{0,1,-1}` |
| Genuine interval algebraic solutions | `Painleve.poleSolution` | On each positive rational interval, packages both derivative certificates, the equation, and `xy-c=0` |
| PII sign symmetry and Riccati reduction | `Painleve.sign_symmetry`, `Painleve.riccati_half` | The Riccati result is explicitly a jet identity, conditional on differentiated Riccati data |

Thus the checked seeds are `y=0` at `α=0`, `y=-1/x` at `α=1`, and
`y=1/x` at `α=-1`. These match the seed convention in
[DLMF §32.8](https://dlmf.nist.gov/32.8).

`AlgebraicRelation` requires an explicit rational point where the defining
polynomial is nonzero. This excludes the vacuous relation `0=0`.
`AlgebraicSolutionOn` ties its relation and ODE to the same value function
and requires first and second `HasDerivativeOnInterval` certificates.
The simple-pole residual theorem holds for positive and negative nonzero
rational inputs; the currently packaged analytic charts are positive intervals.
No value at the pole is treated as a solution.

The generic represented equation interface is an algebraic residual interface.
It does not itself certify that its third and fourth inputs are derivatives.
General non-rational algebraic branches still need branch, denominator-apartness,
and derivative certificates. In particular, `radical_euler` does not construct
a root or prove implicit differentiation.

## Checked Frobenius and Laguerre milestone

The linear and nonlinear developments are separate. The new linear theorem
covers the local regular-singular form

\[
x^2y''+xp(x)y'+q(x)y=0,\qquad
I(s)=s(s-1)+p_0s+q_0,
\]

where `p,q` are finite rational polynomials. For a rational formal exponent
`r` and leading coefficient `c0`, `Fuchs.Frobenius.Equation.coeff` is a
terminating rational algorithm for every requested coefficient. The operator
residual is defined independently, using finite Cauchy products and shifted
Euler operators. Coefficient extraction proves

\[
I(r+n)c_n+\sum_{k<n}((r+k)p_{n-k}+q_{n-k})c_k=0.
\]

| Checked result | Declaration under `Fuchs.Frobenius.Equation` |
|---|---|
| Derive the recurrence from the formal operator | `residual_split` |
| A solution with nonzero leading term requires `I(r)=0` | `indicial_obstruction` |
| Construct a formal solution if `I(r)=0` and `I(r+n)≠0` for every `n>0` | `coeff_isSolution` |
| Uniqueness for the specified leading coefficient | `solution_unique`, `solution_iff_coeff` |
| A zero recurrence denominator requires the lower contribution to vanish | `resonance_compatibility` |
| Every polynomial prefix has zero residual coefficients below its cutoff | `truncation_residual` |

These are **formal coefficient theorems**, not a general analytic Frobenius
convergence theorem. The rational exponent is a formal shift; no branch of
`x^r` is chosen. The total coefficient code uses rational division, but no
correctness theorem drops the nonzero-denominator hypotheses. The regression
`Tests.resonant_no_nonzero_leading` shows why: `x²y''+xy=0` at exponent zero
forces `c0=0` at the resonant degree one.

A complete analytic polynomial application is the normalized Laguerre family

\[
xy''+(b-x)y'+my=0,\qquad b\in\mathbb Q_{>0},\quad m\in\mathbb N.
\]

Its coefficients satisfy
`c(n+1)=(n-m)c(n)/((n+1)(n+b))`. We prove termination above degree `m` for
all `m`, and exact degree `m` when `c0≠0`. `Fuchs.Laguerre.differential_equation`
proves the unmultiplied equation at every rational input, including zero.
`firstDerivativeCertificate` and `secondDerivativeCertificate` certify both
derivatives on any supplied rational interval inside a rational box `[-C,C]`,
`C≥1`. `algebraic_relation` connects that same evaluator to the nonzero graph
polynomial `y-P(x)`. The finite Taylor evaluator is proved equal to the
existing Horner list evaluator by `FormalPowerSeries.eval_truncation`.

Examples with `c0=1` are `1-2x+x²/2` for `(m,b)=(2,1)` and
`1-3x/2+x²/2-x³/24` for `(m,b)=(3,2)`. This normalization fixes the value at
zero; it is not the conventional normalization of every generalized Laguerre
polynomial. The equation agrees with [DLMF 18.8, row 8](https://dlmf.nist.gov/18.8)
with `b=α+1`. Its origin is regular singular, but infinity is irregular: this
is a **local** Fuchs–Frobenius application, not a globally Fuchsian equation.

## Checked effective convergence

`FrobeniusConvergence.lean` handles an indicial root `r` with nonnegative
gap `A = 2*r - 1 + p₀`. Since `I(r+n)=n*(n+A)`, all positive recurrence
denominators are at least `n²`. This includes the larger rational root and
repeated roots. Define the computable bound

```
R = 1 + (|r|+1) * sum(abs(p coefficients)) + sum(abs(q coefficients)).
```

`Equation.coeff_growth` derives `|cₙ| ≤ |c₀|*R^n` from the recurrence. For
rational inputs `R*|x| ≤ 1/2`, `Equation.factorRaw` computes
`[Sₙ - 2|c₀|/2^n, Sₙ + 2|c₀|/2^n]`, where `Sₙ` has the first `n` terms.
`factorRaw_valid` proves orderedness, nesting, and arbitrary rational
precision; `factorRaw_contains_prefix` proves that every later partial sum
is enclosed. The width is exactly `4|c₀|/2^n`; `factorRaw_precision` gives
an executable precision schedule from the existing `halfDecayShift`.

The reusable foundation `GeometricPowerSeries.lean` handles arbitrary signed
coefficient streams with geometric growth, and proves same-stage overlap
for two nonnegative radius choices about the same prefix. Such overlap
identifies a represented value only when both evaluators are valid.

Regressions instantiate the repeated-root modified Bessel equation, a
signed nonterminating recurrence, negative inputs, and a zero leading
coefficient. For the Bessel example the certified radius is `1/6`, and the
box at `x=1/8`, stage 12 has width `1/1024`.

This is convergence of the **Frobenius factor**, not an analytic ODE solution
certificate. Analytic derivatives, a branch of `x^r`, and the smaller
nonresonant root with negative root gap remain future work. The bound is
conservative and makes no optimal-radius claim.

## Lean 4 comparison, inspected 2026-09-22

Comparison here means Lean 4 theorem statements and proof architecture.
Coq/Rocq and Isabelle developments are background only, not the benchmark.
No public Lean 4 Painlevé algebraic-solution classification was located in the
bounded search. This is not a claim that none exists.

| Lean 4 project | Source inspected and comparison |
|---|---|
| [Ripple Frobenius](https://github.com/zinan-huang/Ripple/tree/e9ce148d3975f9e75bb9724e01ec763ad9b368a9/Ripple/Number/Frobenius) | Closest linear comparison. `Indicial.lean` defines shifted Euler operators and proves `indicial_root_of_leading_vanish`. `Substitution.lean` proves `frobeniusSolution_is_solution` under indicial-root and nonresonance hypotheses, uniqueness, and convergence/analyticity under further quantitative hypotheses. Lean/Mathlib 4.30.0; explicitly uses `ℝ`. Source inspected, not independently rebuilt. |
| [Mathlib ODE existence and uniqueness](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/ODE/ExistUnique.html) | Compare derivative semantics, hypotheses and theorem interfaces. Its normed-space and classical-real foundation is not imported here. |
| [Mason–Stothers in Lean 4](https://github.com/seewoo5/lean-poly-abc) | Adjacent algebra comparison: polynomial derivatives, Wronskians, degree bounds and nonexistence arguments. Mason–Stothers and polynomial FLT are integrated into Mathlib. This is not a Painlevé classification. |

Our new `indicial_obstruction`, `coeff_isSolution`, and `solution_unique`
provide concrete theorem-level comparison points with Ripple. Our current
operator has order two, normalized leading coefficient `x²`, and rational
polynomial data; Ripple's inspected construction covers higher-order
polynomial operators and additional convergence results. Our new
`coeff_growth` and `factorRaw_valid` cover nonnegative root gap with explicit
rational boxes; convergence for other roots, analytic differentiation, and
nonintegral branch construction remain missing. Our terminating
Laguerre family instead uses finite rational evaluation and the project's
existing finite-difference certificates, with no infinite-series limit needed.

Searches included public web and GitHub queries for Fuchs/Fuchsian/Frobenius,
regular-singular ODEs, and Painleve/Painlevé in Lean. The indexed Painlevé
matches concerned unrelated removability theorems; Fuchsian-group matches do
not formalize the requested ODE results. Indexing and repository coverage are
incomplete. The earlier [CoRN Picard work](https://users-cs.au.dk/spitters/Picard.pdf),
[Isabelle AFP ODE development](https://isa-afp.org/entries/Ordinary_Differential_Equations.html),
and [Rocq numerical proposal](https://cfhp.univ-lille.fr/files/students/Master-2026-Coqodi.pdf)
are retained only as background references.

## Development plan and open theorems

The present Fuchs target is the linear regular-singularity criterion: its
forward growth implication is checked above, while its converse remains
open. The distinct first-order algebraic differential-equation criterion
associated with Fuchs and Painlevé is reserved for a separate development.
Neither is identified with Picard–Fuchs period equations or Fuchsian groups.

1. **Algebraic differential calculus.** Add normalized finite multivariate
   polynomial and rational-function arithmetic, coefficient reflection,
   degrees, valuations, gcd/resultants, and differential identities.
   Clear denominators only with explicit exclusion or apartness hypotheses.
2. **Algebraic branches.** Strengthen the existing algebraic-function layer
   with nonzero defining polynomials, selected branches, root separation,
   quantitative implicit derivatives, and certified Puiseux charts.
3. **Fuchs.** Extend the checked forward rational-ray growth theorem to
   uniform sector estimates and a general holomorphic-solution adapter, then
   prove the converse criterion. Extend the checked second-order Frobenius convergence theorem to
   the remaining nonresonant roots and analytic derivative certificates; add
   certified nonintegral branches, resonant logarithmic
   solutions and more general local operators. Separately state
   and prove the first-order Fuchs criterion with its precise singularity
   hypotheses. General algebraic-solution/finite-monodromy statements require
   analytic continuation and monodromy infrastructure still absent here.
4. **Painlevé I and II.** Transport the checked regular-factor derivatives to
   the reconstructed pole value, extend to complex charts and computable
   parameters, and prove continuation/exhaustion toward the global Painlevé
   property. Separately prove no rational/algebraic solutions for PI;
   for PII develop pole/degree obstructions, Bäcklund transformations and
   rational-solution constructions at integer parameters, followed by the
   converse/classification and the algebraic-versus-rational bridge.
   The current `c/x` and affine classifications do **not** prove these results.
5. **Painlevé III–VI.** Encode equations with all singular denominators and
   parameter conventions explicit, then certify concrete algebraic examples
   before attempting parameter-dependent classification. These equations
   and their solution classifications are not implemented in this milestone.

No classification theorem is supplied as an axiom, and a formal jet is never
silently promoted to an analytic solution.

## Validation

```sh
lake build ComputableAnalysis.AlgebraicODE.Tests
lake env lean scripts/check_algebraic_ode.lean
```

Regression proofs check both pole signs, reject residue `2`, exclude polynomial
solutions at exponent `1/2`, instantiate the derivative-bearing interval
packages, and connect `-1/x` to the represented-complex equation at every
nonzero rational input. Frobenius regressions cover a repeated indicial root,
a genuine resonance obstruction, two terminating Laguerre polynomials,
and both derivative certificates on an interval containing zero. PI regressions
check a free resonant coefficient, reject quadratic forcing, exercise both
sides of the pole, and bound the nonlinear residual for arbitrary stage-12
box samples.

The new modules contain no `sorry`, `admit`, custom axioms, or `native_decide`
calls (regression computations use kernel-checked `decide`). The exact classification and exact-input runtime bridges print only
standard Lean logical axioms. Generic raw multiplication validity and the
analytic derivative packages inherit existing foundation `native_decide`
axioms; the audit prints these dependencies explicitly. Computable evaluators
do not imply an axiom-free metatheory.

## Number-theoretic application: Apéry

The [Apéry milestone](APERY.md) derives the zeta(3) Picard–Fuchs equation
from integer binomial sums, certifies its local series and three derivatives,
and checks the companion approximants’ exact positive increments. The zeta
identification and irrationality proof remain open.
