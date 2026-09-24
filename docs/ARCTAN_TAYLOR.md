# Arctangent as a function-theory showcase

The central question is why the Taylor polynomials of a smooth real function
can fail to converge at perfectly regular real inputs. The running example is
\[
 S_N(x)=\sum_{k=0}^{N-1}\frac{(-1)^k x^{2k+1}}{2k+1}.
\]
The mathematical convergence interval is \([-1,1]\), including the two
endpoints. The complex derivative has poles at \(\pm i\); arctangent itself
has logarithmic branch points there. Their distance from the origin explains
the radius. This interpretation does not claim that our general
Cauchy-to-Taylor theorem is complete.

## Checked theorem and domain

`ArctanTaylor.convergence_iff` proves, for every **rational input** \(x\),
that the actual partial sums converge to some valid represented real value
if and only if \(|x|\le1\). `geometric_converges` identifies the limit with
the independently constructed geometric arctangent. This reuses the existing
finite rectangle comparison in `PiProofs`; it does not define geometric
arctangent by the series.

`ConvergesTo` tests every output box of the proposed limit against an arbitrary
rational error interval around every sufficiently late partial sum. The
limit must be valid. `convergesTo_isCauchy` derives the ordinary rational
Cauchy condition, and `ConvergesTo.equiv` proves invariance under a change of
representation of the target value. `sample_in_box` connects every ordinary
partial sum, of either parity and either sign of input, to the existing
alternating-series interval evaluator.

For \(r=|x|>1\), `term_lower_bound` proves
\[
 |S_{N+1}(x)-S_N(x)|\ge r(r^2-1)/3>0\qquad(N\ge1).
\]
The proof uses the finite Bernoulli inequality. `not_cauchy` and
`not_converges` therefore exclude **every** valid represented limit. An
invalid raw series evaluator outside its documented domain would not alone
have proved this divergence statement.

## Remaining scope

The input interface for this new classifier is rational. The statement for
arbitrary represented inputs still needs a proved function-evaluation and
representation-invariance extension. The classical theorem displayed in the
reader is labeled with that formalization boundary.

The sharp integrated remainder formula, the distinction between absolute and
conditional convergence, the global complex branch description, and the
positive-input argument transformation in the narrative are mathematical
explanations. The new audit does not certify all of them as separate general
theorems. In particular, formal coefficient differentiation is not silently
promoted to a theorem identifying all analytic derivatives.

The interaction uses browser arithmetic and the browser arctangent function.
It visualizes finite partial sums; no finite plot is used to establish
convergence or divergence. It reports a theoretical error bound, and does not
report a tiny rounded browser difference as an exact zero error.

## Changing the center without computing coefficients

The reader also gives a classical proof that the Taylor series centered at
\(1\) has radius \(\sqrt{2}\). On the convex open disk avoiding \(\pm i\),
polygonal path independence constructs the integral of \(1/(1+z^2)\),
normalized to the existing arctangent value at \(1\). Cauchy–Taylor gives the lower bound.
For the upper bound, a hypothetical sum on a larger disk would satisfy
\((1+z^2)T'(z)=1\) throughout that disk by the identity theorem; evaluation
at \(i\) is impossible. The proof does not compute Taylor coefficients and
does not decide convergence at real boundary points.

This is mathematical exposition, not an additional Lean result. The analytic
bridges on arbitrary represented complex inputs remain to be formalized.
The new geometric interaction draws disks centered at \(1\) and the fixed
singularities. It does not numerically generate a Taylor expansion at \(1\).

## Verification

Build `ComputableAnalysis.ArctanTaylorConvergence`, then run
`lake env lean scripts/check_arctan_taylor.lean`. The audit checks actual
elaborated dependencies, verifies reuse of the geometric bridge, rejects
Mathlib imports and unfinished proofs, and prints inherited native-decision
axioms. The publication workflow also runs desktop and mobile interaction
checks before deploying the page.
