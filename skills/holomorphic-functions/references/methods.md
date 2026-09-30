# Choosing a holomorphicity proof

These are function-specific proof routes. They are not additional definitions
of holomorphicity and do not assert generic constructors that have not been
implemented. Each route must eventually supply the existing represented
`Map` and `HolomorphicOn` evidence, with arbitrary valid inputs in its domain.

## Finite algebra and composition

For pointwise derivatives, construct the continuous divided difference in
`DerivativeAt`. Constant and identity quotients are literal constants; the
sum, product, and chain rules construct the others. The product quotient is
\(Q^f_a(y)g(y)+f(a)Q^g_a(y)\), and the composition quotient is
\(Q^g_{f(a)}(f(y))Q^f_a(y)\). Continuity at the center suffices.
`PolynomialFunction.derivativeContinuation` and its iterated and real
restriction constructors already provide this evidence.

For polynomials, use `PolynomialFunction.ofCoefficients` or finite
`PolynomialFunction` expressions. Their `holomorphic`, `hasDerivative`, and
`iterated_hasDerivative` constructors cover arbitrary represented coefficients
and inputs. `derivative_holomorphic` supplies the derivative-map witness needed
by the ODE interface. Direct remainder identities remain useful for tighter
function-specific radii; the square and affine examples are checked.
For a rational expression, find a strictly positive rational denominator margin on that
whole neighborhood before division. For sums, products, and compositions
of supplied holomorphic maps, use `HolomorphicOn.add`, `mul`, and `comp`
from `HolomorphicFoundation`. These construct quotient derivatives and the
correct open domains. The older `HolomorphicCalculus` rules also retain
separately supplied derivative continuity for legacy clients. Composition uses the inverse-image domain and computes local image
control. `Holomorphic.continuous` derives continuity of the original function;
`Holomorphic.congr` changes to an equivalent evaluator on the same domain.

Keep the coordinate product constant:
\[
\|uv\|_\infty\le2\|u\|_\infty\|v\|_\infty.
\]
For \(\sin(1/z)\), first separate \(z\) from zero on a neighborhood,
construct reciprocal bounds, and use a certified complex sine chart on its
image. Its zeros \(1/(n\pi)\) approach an excluded point; they do not establish
local equality with zero anywhere in the punctured plane. The general
reciprocal/rational adapter and sine chart still need to be
constructed; the composition rule is now available.

## Direct power series

On a smaller closed disk than the supplied convergence disk, control the
value tail, the differentiated tail, and a second-order remainder majorant.
With \(h=z-a\), prove the finite binomial identity and bound
\[
f(a+h)-f(a)-f'(a)h.
\]
For the quotient foundation, sum the finite divided-difference polynomials
with a certified tail uniform near the center, prove the exact factorization,
and prove continuity at the center. Convergence of the value series alone
does not justify this passage. Bound the differentiated series' variation
separately when a legacy client needs derivative continuity. A factorial or
geometric majorant with an executable cutoff is sufficient; first proving
that every holomorphic function has a Taylor expansion is unnecessary.
For arbitrary represented centers, transfer finite polynomial identities to
raw evaluations and prove the infinite-tail comparison. The existing
rational-input Cauchy–Taylor theorem does not do this automatically.

## Real partial derivatives

For a specific \(f=u+iv\), construct real differentiability estimates for
both components with a common neighborhood and prove the Cauchy–Riemann
identities there. Combine the two linear remainders to get multiplication by
\(u_x+iv_x\). Coordinate partial derivatives satisfying the identities at
one point are insufficient without a total differentiability estimate.
The required component calculus adapters are not currently general Lean
constructors.

## Particular integrals and differential equations

For a parameter-dependent definite integral, prove whole-path denominator
separation and quantitative bounds for the parameter derivative and its
remainder before exchanging a limit and that particular integral. Control
endpoint and improper tails as well when present. Do not appeal to a
universal differentiation-under-the-integral operator.

For an ODE, construct the local solution with certified coefficients or an
integral iteration, prove the equation and derivative continuity, and prove
local uniqueness separately when it is used to compare continuations.
A formal recurrence alone does not prove a holomorphic solution exists.

## Reflection and locally coherent charts

`Holomorphic.reflect` is now checked for
\[
f^*(z)=\overline{f(\overline z)},\qquad
(f^*)'(z)=\overline{f'(\overline z)}.
\]
It uses the reflected **open** domain and preserves the supplied radii.
`AgreeAt.reflect` transports overlap agreement. Conjugating the output alone
usually gives an antiholomorphic function, so retain both conjugations.
This does not prove the Schwarz boundary-seam theorem.

`Realization.holomorphic` constructs an evaluator from a total chart selector
and local germ coherence. Its raw evaluation at \(z\) is the selected chart's
evaluation at \(z\); representation invariance and the derivative follow by
proof. Supply executable chart selection and radii in concrete applications.
No decision of domain membership or selection of quotient representatives is
required. Deriving local coherence from arbitrary continuation chains remains
a distinct theorem.

## Identity theorem: use only at its checked scope

The classical argument factors a nonzero Taylor expansion as
\[
f(z)=(z-a)^m\bigl(c_m+(z-a)h(z)\bigr).
\]
A positive lower bound for \(|c_m|\), together with a tail bound, gives an
explicit punctured neighborhood without zeros. Construct the coefficient
separation evidence when claiming an executable radius. Do not silently
assume that one can decide which arbitrary represented coefficient is the
first nonzero one. The general identity theorem and the reconstruction needed
to apply this argument to every `Holomorphic` witness remain open.

## Proof sources and checks

Read [the holomorphic examples](../../../ComputableAnalysis/HolomorphicExamples.lean),
[reflection](../../../ComputableAnalysis/Continuation/Reflection.lean), and
[realization](../../../ComputableAnalysis/Continuation/Realization.lean).
Build `ComputableAnalysis.Continuation` and run
`lake env lean scripts/check_continuation.lean`. For the full distinction
between checked laws and remaining constructions, see
[the ledger](../../../docs/ANALYTIC_CONTINUATION.md).
