# Function-specific improper power integrals

The power tests now apply to **every valid represented-real exponent**, including
irrational exponents. Lean checks the exact improper values and all three
convergence classifications:

\[
\int_0^1 x^{-p}\,dx\simeq\frac1{1-p}\quad(p<1),\qquad
\int_1^\infty x^{-p}\,dx\simeq\frac1{p-1}\quad(p>1),
\]

\[
\int_0^1x^{-p}\,dx\text{ converges}\iff p<1,\qquad
\int_1^\infty x^{-p}\,dx\text{ converges}\iff p>1,\qquad
\sum_{n=1}^\infty n^{-p}\text{ converges}\iff p>1.
\]

Here a strict inequality is certified by a finite input enclosure separated
from one. The algorithms search for that enclosure; callers do not choose an
internal precision schedule or an exponent chart. Divergence uses weak order,
so the boundary case is included without an equality decision.

## Finite intervals, not a compactness theorem

A “compact integral” in the source means a definite integral over a finite
closed rational interval separated from zero. No topological compactness
principle, abstract completion, Mathlib real numbers, or custom axioms are
introduced. All new audited roots use only Lean's standard logical axioms.
The compact endpoints are rational; the exponent is an arbitrary valid
represented real. Extension to arbitrary represented endpoints is not claimed.

The dependency order is:

1. Independently compute powers using finite generalized-binomial polynomials
   and rational interval bounds, uniform in a bounded exponent interval.
2. Construct actual finite-interval integral witnesses from finite polynomial
   integrals. Reflection handles the interval below one. A proved reciprocal
   substitution handles the interval above one, without crossing zero.
3. Prove finite endpoint error estimates, then construct improper limits and
   identify them with the independent reciprocal computation.
4. Prove positivity and monotonicity of the power evaluator. Certified unit
   rectangles give finite sum–integral comparisons, hence the series test.

The finite binomial identities have been extracted from `ZetaReal.Dirichlet`
into `BinomialPowerPolynomial`. The power-integral proofs do not import a
completed zeta or Dirichlet series calculation. No series convergence theorem
is used to justify the improper integral that later proves convergence.

`Integral.HasIntegral` is a checked sufficient rectangle specification, not
a mandatory definition of every future integral. `HasIntegralLimit` requires
actual compact witnesses and convergence against all such witnesses. Its
uniqueness law is proved, not assumed as a certificate field.

## Exact finite-interval identities

`PowerCompactIntegral.compact_hasIntegral` constructs the integral on
\(0<a\le b\le1\), with

\[
(1-p)\int_a^b x^{-p}\,dx\simeq b^{1-p}-a^{1-p}.
\]

`PowerInfinityIntegral.infinityCompact_hasIntegral` constructs it on
\(1\le a\le b\), with

\[
(p-1)\int_a^b x^{-p}\,dx\simeq a^{1-p}-b^{1-p}.
\]

These division-free identities also make sense at the boundary exponent.
They do not assert a separately proved logarithm identity. Each integrand is
an independent binomial computation; endpoint agreement is a theorem, not its
definition as an integral.

## The function-specific endpoint estimate

Let \(c_{s,k}\) be the finite binomial coefficients for \((1-z)^{s-2}\).
On a rational exponent interval
\(1+1/(q+1)\le s\le m+2\), set

\[
B_m=(m+3)^{m+1},\quad r_q=\frac{2q+2}{2q+3},\quad
K_j=(m+1)2^j,\quad a_j=\frac{2^{-j}}{1+K_jB_m}.
\]

The independently integrated finite polynomial
\(J_{s,L}(z)=\sum_{k<L}c_{s,k}z^{k+1}/(k+1)\) obeys

\[
\left|J_{s,L}(1-a)-\frac1{s-1}\right|
\le E_j:=2(q+1)B_m r_q^j+2^{-j}
\quad(0\le a\le a_j,\ L\ge K_j).
\]

This is a **finite rational inequality**. It follows from a telescoping
coefficient difference, a finite endpoint identity, and finite polynomial
variation. Both \(a_j\to0\) and \(E_j\to0\) have explicit rational searches.
For the zero endpoint use \(s=2-p\); for infinity use \(s=p\).
The bounds transfer to all output boxes of the represented computations.

Public classifications use the fixed dyadic exhaustions
\([2^{-(2n+1)},1]\) and \([1,2^{2n+1}]\). Agreement with the internal
function-specific cutoff follows from the same estimate for every smaller
positive cutoff. The supplied-integral theorems identify **any** witness on
these exhaustions with the reciprocal formula using `RealRaw.Equiv`.

## Finite comparison, computation, and divergence

For nonnegative \(p\), positivity and monotonicity are proved for the independent
power evaluator. Unit-cell bounds give

\[
\int_{N+1}^{M+1}x^{-p}\,dx\le
\sum_{n=N+1}^{M}n^{-p}\le\int_N^M x^{-p}\,dx.
\]

For \(p>1\), `RealPowerSeries.series` chooses a finite truncation using the
proved integral error, computes the finite sum to a rational width budget,
and obtains a rational candidate \(c_n\). Its nested output is the intersection
of the first \(n+1\) boxes

\[
[c_j-3\cdot2^{-j},\ c_j+3\cdot2^{-j}],\qquad 0\le j\le n.
\]

Validity, output width at most \(6\cdot2^{-n}\), convergence to the independent
partial sums, uniqueness, and invariance under changing the exponent's
representation are proved. This general constructor is a conservative
computability reference: its truncations can be very large, especially near
one. It is not presented as an efficient high-precision numerical zeta routine.
The earlier integer constructors remain available with much sharper bounds.

For \(p\le1\), the power terms dominate harmonic terms, giving
\(S_{2^{2T}}\ge T\). For improper divergence, each dyadic harmonic lower
rectangle has area \(1/2\). The same finite rectangles bound the appropriate
power integrals below and rule out every finite represented limit. Compact
witnesses are constructed even in these divergent cases.

## Public theorems and verification

`RealPowerIntegralTest` exports `zero_converges_iff`,
`infinity_converges_iff`, `series_integral_test`, `zero_supplied_exact`, and
`infinity_supplied_exact`. `PowerDivergence.series_converges_iff` gives the
series classification. The root library imports these modules.

```sh
lake build ComputableAnalysis
lake env lean scripts/check_power_improper.lean
lake env lean scripts/check_real_power_integrals.lean
python3 scripts/audit_construction_first.py
python3 scripts/audit_integral_enclosures.py
python3 blueprint/checks/check_foundation_imports.py
```

The new audit covers 28 theorem roots and 19 executable regression groups,
including noninteger and irrational exponent formulas, finite endpoint errors,
and independent finite-interval evaluation. It supplements the earlier
28-root, 34-group integer audit. Numerical tests supplement the proofs; they do
not establish the formulas or benchmark the general infinite-series constructor.

Gaussian normalization, the Gamma integral, and identification of the ball
formula with geometric volume remain separate work. No new completion of
those bridges is claimed here.
