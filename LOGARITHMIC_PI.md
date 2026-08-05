# Finite logarithmic π computations

`ComputableAnalysis/LogarithmicPi.lean` contains two independently executable
forms of the supplied arctangent integration-by-parts formula:

\[
  4\int_0^1\arctan(x)\,dx+2\int_1^2\frac{dx}{x}\ \Equiv\ \pi_{\rm area},
\]

and the same endpoint evaluated after the rational substitution (t=x^2).

Both are finite rational-box computations.  The reciprocal-integral form has
width at most (52/2^n); the square-pullback form has width at most
(56/2^n).  Their agreement is proved before either is identified with the
geometric arctangent endpoint.

The module deliberately does **not** claim that either endpoint is the
project's future canonical logarithm.  That transport belongs to the
exp/log-uniqueness route, not to this finite integration certificate.

Useful declarations:

- `LogarithmicPi.reciprocalRaw`, `LogarithmicPi.reciprocalRaw_valid`
- `LogarithmicPi.reciprocalRaw_width_le`
- `LogarithmicPi.reciprocalRaw_equiv_piCircleArea`
- `LogarithmicPi.squareSubstitutionRaw`
- `LogarithmicPi.squareSubstitutionRaw_equiv_reciprocalRaw`
- `LogarithmicPi.squareSubstitutionRaw_equiv_piCircleArea`
