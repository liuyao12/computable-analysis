# Powers and improper endpoints

The power tests ask opposite questions at zero and infinity: does the function grow too quickly near a missing endpoint, or decrease too slowly along a tail? The [checked guide](../../../docs/POWER_IMPROPER.md) develops the thresholds. This recipe organizes the finite integral and the omitted-endpoint budget needed to prove them.

Keep three computations separate: the power function, the finite-interval
integral, and the improper limit. Follow the
[shared formalization policy](../../../FORMALIZATION_GUIDE.md#computable-foundations-exact-mathematical-theorems)
and the [checked power-integral guide](../../../docs/POWER_IMPROPER.md).

## Establish the finite integral first

The current route computes powers from finite binomial polynomials with
uniform rational bounds in the exponent. It constructs actual finite-interval
integral witnesses, then proves the endpoint identities. The exponent may be
irrational; the current finite truncation endpoints are rational.

Below one, the division-free identity is

\[
(1-p)\int_a^b x^{-p}\,dx\simeq b^{1-p}-a^{1-p},
\qquad 0<a\le b\le1.
\]

Above one, a justified reciprocal substitution gives the corresponding
finite-interval formula. Do not infer either integral from a valid numerical
candidate or use an already completed infinite series to justify it.

## Choose the endpoint allowance

For \(p<1\) at zero or \(p>1\) at infinity, search the input boxes for an
observable strict gap from one. The hypothesis proves search termination.
Never branch on undecidable equality with one.

The checked endpoint estimate uses \(s=2-p\) at zero and \(s=p\) at infinity.
On a certified chart \(1+1/(q+1)\le s\le m+2\), put

\[
B_m=(m+3)^{m+1},\quad r_q=\frac{2q+2}{2q+3},\quad
K_j=(m+1)2^j,\quad a_j=\frac{2^{-j}}{1+K_jB_m}.
\]

The finite integrated polynomial obeys

\[
\left|J_{s,L}(1-a)-\frac1{s-1}\right|
\le E_j=2(q+1)B_mr_q^j+2^{-j}
\quad(0\le a\le a_j,\ L\ge K_j).
\]

Use this proved finite estimate to certify the improper limit. For a requested
tolerance, choose a stage where the endpoint allowance and finite-computation
error fit the budget. Keep the concrete lower and upper rational output bounds
available beneath the exact reciprocal identity.

## Compare finite sums and prove divergence

For nonnegative exponents, prove positivity and monotonicity of the independent
power evaluator, then compare finite sums with finite integrals on unit cells.
Only afterward construct the infinite sum. For the divergent regimes, transfer
finite harmonic lower bounds; the critical exponent requires no logarithm
identity or equality decision.

The public results are the exact values \(1/(1-p)\) and \(1/(p-1)\) on their
convergent domains, and all three power-test classifications. The general
series constructor is conservative and may require enormous truncations.
Retain the sharper integer algorithms when they apply.

## Proof sources and checks

Use [RealPowerIntegralTest](../../../ComputableAnalysis/RealPowerIntegralTest.lean),
[the finite endpoint proof](../../../ComputableAnalysis/BinomialEndpointBounds.lean),
and [the independent series construction](../../../ComputableAnalysis/RealPowerSeries.lean).
Run `lake env lean scripts/check_real_power_integrals.lean` and
`lake env lean scripts/check_power_improper.lean` after relevant changes.

Preserve the proved representation invariance and agreement between internal
cutoffs and the public dyadic exhaustions. These results do not establish a
general Gamma integral or arbitrary represented finite endpoints.
