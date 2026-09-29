# Trigonometric functions

Specify the angle convention first. The reader's circle coordinates use
\(\cos(\pi x)\) and \(\sin(\pi x)\). Preserve that normalization when applying
derivative, substitution, or period formulas. Follow the
[shared formalization policy](../../../FORMALIZATION_GUIDE.md#computable-foundations-exact-mathematical-theorems).

## Construct the finite approximation

Use the independent circle-coordinate evaluator to enclose the function on
each interval. Prove coordinate order on monotone pieces, or supply a quantitative
variation bound. These whole-cell ranges give elementary lower and upper
step functions whose finite integrals enclose the proposed value.

For an inexact turning point, use shrinking rational brackets. Bound the
unresolved interval by its width times a proved height bound. Do not decide
equality with a represented turning point, and do not impose turning-point data
on the final caller when the construction can produce it.

## Worked route: the cosine-square integral

On \([0,1/2]\), the function \(f(x)=\cos^2(\pi x)\) decreases from one to
zero. With \(h=1/(2N)\), exact-value endpoint sums satisfy

\[
L_N=h\sum_{k=1}^{N}f(kh),\qquad
U_N=h\sum_{k=0}^{N-1}f(kh),\qquad U_N-L_N=h.
\]

At runtime, replace each endpoint value by its certified rational box. If each
box has width at most \(\eta\), the enclosing lower/upper sum gap is at most
\(h+\eta\). Choose both subdivision and value precision. Numerical endpoint
sampling without a whole-cell bound does not give an enclosure.

Reflection gives \(f(x)+f(1/2-x)=1\), suggesting the exact value \(1/4\).
Justify reflection for the supplied integrals, then identify the independent
computation. The reader's checked cosine-square example also supplies a finite
FTC route and an Euler route; retain their actual hypotheses and provenance.

## Rational trigonometric expressions

Certify every denominator on the whole interval. A half-angle substitution
can reduce the expression to a rational function, but it needs a proved
change-of-variable comparison, chart orientation, and coverage. Split and
compare charts where the substitution has a pole. Algebraic substitution alone
is not a definite-integral theorem. Continue with the
[rational-function skill](rational-function-integrals.md).

## Arbitrary endpoints and periodicity

Use periodicity to control rational approximants, with an endpoint error bound
to pass to arbitrary represented endpoints. Do not require a decision of which
side of a period boundary a represented real occupies. Prove agreement on chart
overlaps and at boundaries. State the final identity, for example,

\[
\int_0^x\cos^2(\pi t)\,dt
\simeq\frac{x}{2}+\frac{\sin(2\pi x)}{4\pi},
\]

over every valid represented endpoint in its genuine domain.

## Proof sources and checks

Read the maintained [cosine-square exposition](../../../book/cosine-square/page.html)
and [rational/trigonometric progress report](../../../docs/RATIONAL_PRIMITIVES.md).
The cosine-square page links its pinned checked source; the general rational
trigonometric assembly has a different, incomplete proof status.

Check interval bounds, shrinking turning-point errors, period-boundary agreement,
and representation invariance. Run the relevant theorem audits using the
[formalization skill](../../computable-analysis-formalization/SKILL.md). Do not
extend the checked cosine-square result to a whole family without its bridges.
