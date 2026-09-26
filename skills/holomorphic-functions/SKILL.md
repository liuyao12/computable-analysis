---
name: holomorphic-functions
description: Prove that a specific represented complex function is holomorphic in this repository, supplying a complex derivative, rational error radii, and derivative continuity. Use for function-theory constructions and analytic adapters, not merely formal jet algebra.
---

# Proving specific functions holomorphic

Read the [formalization policy](../../FORMALIZATION_GUIDE.md#computable-foundations-exact-mathematical-theorems)
and use the existing computable-analysis foundation. The checked interface is
[`FunctionTheory.Holomorphic`](../../ComputableAnalysis/Holomorphic.lean).
The worked constructions are in
[`HolomorphicExamples.lean`](../../ComputableAnalysis/HolomorphicExamples.lean).

## Choose the mathematical contract

Our working notion supplies an open domain, a represented function and its
complex derivative, local derivative-error radii, and continuity moduli for
the derivative. It deliberately asks for more data than the classical
pointwise definition. Do not spend the task proving equivalence with the
weakest definition unless requested. `HasDerivativeAt` is the underlying
first-order property and does not itself assume derivative continuity.

The domain and evaluator must respect `ComplexRaw.Equiv`. Prove validity for
all valid represented inputs in the domain, including irrational inputs and
coefficients. `Map.eval` is total as a raw function; its behavior outside the
domain has no mathematical significance. Keep branch restrictions and pole
separation explicit. `OpenDomain` gives a positive rational neighborhood of
each valid domain point; do not identify an open domain with a single closed
rational rectangle.

`Small u r` is an exact coordinate bound on the represented value, expressed
using `RealRaw.Le`. It means
\[
 \|u\|_\infty\le r,
 \qquad \|u\|_\infty=\max(|\Re u|,|\Im u|).
\]
It does not require early output boxes to fit inside that rectangle.
`Small.congr` transports the bound between valid equivalent representations.

## Construct the evidence

1. Implement the value and proposed derivative with rational boxes; prove
   validity and representation invariance. Formal jet operations can propose
   the derivative but are not proof that it differentiates the value.
2. Derive a finite identity or estimate for
   \[
   f(z)-f(a)-d(a)(z-a).
   \]
   Prove it for the actual represented evaluations. A rational-input identity
   is useful only after its box containment or approximation bridge is proved.
3. For each positive rational \(\varepsilon\), give a positive rational
   \(\delta\). For every valid domain point \(z\) and positive rational
   \(H\le\delta\), prove
   \[
   \|z-a\|_\infty\le H
   \quad\Longrightarrow\quad
   \|f(z)-f(a)-d(a)(z-a)\|_\infty\le\varepsilon H.
   \]
   This quantifies over every complex direction. Checking only real increments
   is insufficient. Keeping \(H\) rational avoids constructing a norm value
   or dividing by an uncertain displacement.
4. Independently give the local modulus for \(d\): for each requested
   \(\varepsilon\), a positive rational \(\eta\) such that
   \[
   \|z-a\|_\infty\le\eta
   \quad\Longrightarrow\quad
   \|d(z)-d(a)\|_\infty\le\varepsilon.
   \]
5. Package `Holomorphic`. Use `HasDerivativeAt.congrPoint` and
   `congrDerivative` to transport witnesses; do not equate finite boxes or
   silently change branches.

Choose the numerical method for the function, not a universal recipe:

- **Affine functions:** the remainder is exactly zero. The checked example
  allows arbitrary valid represented slope and intercept; its derivative is
  constant and its continuity estimate is zero.
- **Polynomials:** finite algebra gives a quadratic remainder on a bounded
  neighborhood. Bound its coefficients, then choose the radius from that
  bound. The checked square example uses
  \(2H^2\le\varepsilon H\) and \(\delta=\varepsilon/2\).
  The coordinate maximum norm satisfies
  \(\|uv\|_\infty\le2\|u\|_\infty\|v\|_\infty\), not a
  submultiplicative estimate with constant one.
- **Rational functions:** certify denominator separation on a neighborhood;
  derive the quotient remainder and derivative continuity with that margin.
  This is a strategy; a generic adapter is not yet supplied by this module.
- **Series or elementary charts:** bound the value tail, derivative tail,
  and first-order remainder with explicit schedules. Precision may depend
  on the displacement bound. Obtain derivative continuity from an independent
  local estimate. Existing jets and rational-point secant estimates still
  need their represented-input bridges.

Computability of a function alone does not imply differentiability or provide
an algorithm for its derivative. Nor is continuity generally decidable.
A Type-2 computable derivative is continuous on its represented domain, but
`ComplexRaw → ComplexRaw` alone does not certify a Type-2 realizer. Construct
the continuity evidence used here instead of claiming the type supplies it.

## Keep the scope honest

Do not include Cauchy's formula, power-series equality, or vanishing contour
integrals as fields of a holomorphicity witness. Those are subsequent theorems.
Pointwise moduli do not automatically give an executable uniform mesh on a
rectangle. Construct any uniform local approximation and whole-edge enclosure
data needed by a particular Cauchy application. Prefer those specific
rectangular computations over a universal polygon-integral operator.

Run `lake build ComputableAnalysis.HolomorphicExamples` and
`lake env lean scripts/check_holomorphic.lean`, plus the affected client and
repository checks. Inspect the hypotheses and report which functions now
have actual witnesses; a newly declared interface alone is not a completed
example.
