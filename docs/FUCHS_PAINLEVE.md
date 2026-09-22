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

## Research comparison, checked 2026-09-22

I did not locate a public, inspectable formalization of the Fuchs–Painlevé
algebraic-solution classification in the searches below. This is a bounded
search result, not a claim that none exists.

| Project or source | Verified status | Useful comparison |
|---|---|---|
| [CoRN/MathClasses Picard algorithm](https://users-cs.au.dk/spitters/Picard.pdf), Makarov and Spitters; [public ODE source](https://github.com/EvgenyMakarov/corn/tree/master/ode) | Published constructive Picard–Lindelöf development, with Coq files for Picard iteration, integration, and Banach fixed points | Closest foundation-level comparison: efficient constructive exact reals and explicit correctness hypotheses. Its completion/function-space machinery differs from our finite interval certificate route; it does not classify Painlevé algebraic solutions. |
| [Isabelle AFP: Ordinary Differential Equations](https://isa-afp.org/entries/Ordinary_Differential_Equations.html), Fabian Immler and Johannes Hölzl | Existing formal ODE development: Picard–Lindelöf, flows, linear ODEs; associated verified numerical enclosure sessions | Existence/uniqueness and numerical enclosure specification. Its HOL analysis foundation differs from our rational-interval foundation. It is not a Fuchs/Painlevé algebraic-solution classification. |
| [Solving Differential Equations in Rocq](https://cfhp.univ-lille.fr/files/students/Master-2026-Coqodi.pdf), Bréhard/Pous/Brisebarre, spring 2026 | Research/internship proposal explicitly lists Painlevé I among planned examples | Closest topical lead for validated computations. The document proposes error-bounded ODE approximation using Interval and ApproxModels; it is not evidence of a completed implementation or an algebraic classification. |
| [Mason–Stothers and corollaries in Lean 4](https://arxiv.org/abs/2408.15180), Baek and Lee | Paper reports formal proofs integrated into Mathlib | Polynomial degree/derivative arguments and algebraic nonexistence proofs; compare proof organization without importing its real analysis. This is adjacent algebra, not a Painlevé formalization. |
| [DLMF Chapter 32](https://dlmf.nist.gov/32) | Mathematical reference, not a proof-assistant project | Equation conventions, rational seeds, Bäcklund transformations, and later comparison targets |

Searches covered web queries combining Fuchs/Fuchsian/Painlevé/Painleve with
Lean, Coq/Rocq, Isabelle, formalization, and formal verification; GitHub
repository search for Painleve and Coqodi; and code queries for Painleve in
Lean, Coq, and Isabelle, accented Painlevé in Lean, and Fuchsian in Lean.
Returned matches concerning Fuchsian *groups*, Painlevé removability, and
Painlevé–Gullstrand coordinates do not address these differential equations.
Computer-algebra and numerical Painlevé packages also appeared, but their
existence is not evidence of a kernel-checked mathematical formalization.
GitHub indexing and search coverage are incomplete. ApproxModels was linked
by the Rocq proposal; its repository could not be inspected through the web
fetch because the host denied access.

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
3. **Fuchs.** Develop regular-singular local equations, indicial polynomials,
   resonances, Frobenius recurrences and convergence bounds. Separately state
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
nonzero rational input.

The new modules contain no `sorry`, `admit`, custom axioms, or `native_decide`
calls. The exact classification and exact-input runtime bridges print only
standard Lean logical axioms. Generic raw multiplication validity and the
analytic derivative packages inherit existing foundation `native_decide`
axioms; the audit prints these dependencies explicitly. Computable evaluators
do not imply an axiom-free metatheory.
