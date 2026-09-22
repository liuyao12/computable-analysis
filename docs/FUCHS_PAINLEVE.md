# Fuchs–Painlevé algebraic differential equations

This is an independent subproject of Computable Analysis, alongside the PDE
work. Import `ComputableAnalysis.AlgebraicODE`. It uses this repository's
`Rat`, `QComplex`, `ComplexRaw`, overlap equivalence, and two-sided rational
finite-difference certificates. There is no Mathlib dependency or Mathlib real.

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
polynomial operators and additional convergence results. Our general
convergence and nonintegral branch construction remain missing. Our terminating
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

“Fuchs” includes two distinct directions. We start with the Euler member of
regular-singular linear equations, but reserve a separate development for
Fuchs's first-order algebraic differential-equation criterion underlying
the Painlevé classification. Neither is identified with Picard–Fuchs period
equations or with Fuchsian groups.

1. **Algebraic differential calculus.** Add normalized finite multivariate
   polynomial and rational-function arithmetic, coefficient reflection,
   degrees, valuations, gcd/resultants, and differential identities.
   Clear denominators only with explicit exclusion or apartness hypotheses.
2. **Algebraic branches.** Strengthen the existing algebraic-function layer
   with nonzero defining polynomials, selected branches, root separation,
   quantitative implicit derivatives, and certified Puiseux charts.
3. **Fuchs.** Extend the checked second-order formal Frobenius construction to
   convergence bounds, certified nonintegral branches, resonant logarithmic
   solutions and more general local operators. Separately state
   and prove the first-order Fuchs criterion with its precise singularity
   hypotheses. General algebraic-solution/finite-monodromy statements require
   analytic continuation and monodromy infrastructure still absent here.
4. **Painlevé I and II.** Prove no rational/algebraic solutions for PI;
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
and both derivative certificates on an interval containing zero.

The new modules contain no `sorry`, `admit`, custom axioms, or `native_decide`
calls (regression computations use kernel-checked `decide`). The exact classification and exact-input runtime bridges print only
standard Lean logical axioms. Generic raw multiplication validity and the
analytic derivative packages inherit existing foundation `native_decide`
axioms; the audit prints these dependencies explicitly. Computable evaluators
do not imply an axiom-free metatheory.
