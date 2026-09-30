# Holomorphic functions from represented computations

The working notion supplies a function and a **continuous complex derivative**
on an open domain. We choose sufficient data for the intended function theory;
we do not first prove the broadest existence criterion. The weaker local
first-order condition is separately available as `HasDerivativeAt`.

For every valid represented point \(a\), supply a valid derivative value
\(d(a)\). For every positive rational \(\varepsilon\), supply a positive
rational \(\delta\) such that, for all valid represented domain points \(z\)
and positive rational \(H\le\delta\),
\[
 \|z-a\|_\infty\le H
 \quad\Longrightarrow\quad
 \|f(z)-f(a)-d(a)(z-a)\|_\infty\le\varepsilon H.
\]
Here \(\|u\|_\infty=\max(|\Re u|,|\Im u|)\). `Small` expresses the
corresponding closed coordinate bound directly through `RealRaw.Le` and
rational endpoints; no norm-valued computation or square root is required.
Quantifying over every rational upper bound \(H\) gives relative first-order
control without dividing by an uncertain represented displacement.

The domain has supplied positive rational neighborhoods. Function values,
domain membership, and derivative values respect equivalent valid input
representations. A separate local continuity modulus bounds
\(\|d(z)-d(a)\|_\infty\) by \(\varepsilon\) on a supplied neighborhood.
Neither a contour identity nor power-series representation is assumed.

## Continuity of represented values

Use `RepresentedContinuity` for continuity at a point and throughout a domain.
For a valid represented real point \(a\in D\), `RealFunctionTheory.ContinuousAt`
supplies, for every positive rational \(\varepsilon\), a positive rational
\(\delta\) satisfying
\[
 y\in D,\quad |y-a|\le\delta
 \quad\Longrightarrow\quad |f(y)-f(a)|\le\varepsilon.
\]
The inequalities use arithmetic and `RealRaw.Le` on represented values.
`RealFunctionTheory.Small u r` means \(-r\le u\le r\). For complex values,
`FunctionTheory.ContinuousAt` uses the same law with the coordinate maximum
norm. Both quantify over arbitrary valid represented neighbors.

`ContinuousOn` supplies this law at every valid domain point. Its radius may
depend on the point and tolerance; this is not uniform continuity.
`ContinuousOn.atPoint` extracts a local witness and `ofAtPoint` assembles
supplied local witnesses, without choosing a uniform radius.
`ContinuousAt.congrPoint` and `congrEval` prove invariance under equivalent
valid input names and equivalent evaluators; the radius computation is reused.
Neither a common finite output stage nor any required approximation recipe
is part of the public law. Finite interval estimates are proof tools underneath.
The older rational-input `EffectiveContinuous` and interval
`EpsilonDeltaContinuousOn` are specialized finite estimates, not the definition
of continuity for all represented inputs. A raw evaluator alone does not
supply continuity evidence.

The real identity and arbitrary valid represented constants have constructed
witnesses. `HasDerivativeAt.continuous` derives continuity at one point from
its derivative remainder estimate, without derivative continuity or an open
domain. `Holomorphic.continuous` assembles those witnesses throughout its domain.

## Checked constructions

`affine_holomorphic` constructs the full interface for
\[
 f(z)=cz+b,\qquad d(z)=c,
\]
with arbitrary valid represented complex coefficients \(c,b\).
`affine_remainder` proves that its represented remainder is equivalent to
zero. This is an exact statement about represented values, even though
independent interval arithmetic can give a nonzero-width remainder box.

`square_holomorphic` constructs the full interface for
\[
 f(z)=z^2,\qquad d(z)=2z.
\]
A finite rational identity is lifted to represented inputs by box containment:
\[
 f(z)-f(a)-2a(z-a)\simeq(z-a)^2.
\]
`Small.mul` proves the coordinate bound
\(\|uv\|_\infty\le2\|u\|_\infty\|v\|_\infty\).
Thus \(\delta=\varepsilon/2\) controls the derivative remainder, while
\(\eta=\varepsilon/2\) controls derivative continuity. Both radius
computations are executable. `HasDerivativeAt.congrPoint` and
`congrDerivative` preserve the same quantitative law under equivalent valid
representations of the base point and derivative.

## Completed calculus rules

`HolomorphicCalculus` now constructs continuity of the function itself and
holomorphic sums, products, and compositions. The sum and product use the
intersection of the original domains. The composition uses exactly
\[
D_{g\circ f}=\{z\in D_f:f(z)\in D_g\}.
\]
Its open-domain radius combines the inner domain radius with a continuity
radius that keeps the image inside the outer domain. No decision procedure
for domain membership or nonzero values is introduced.

The derivative rules are actual `HasDerivativeAt` witnesses, including their
rational error radii:
\[
(f+g)'=f'+g',\qquad (fg)'=f'g+fg',\qquad (g\circ f)'=(g'\circ f)f'.
\]
The derivative's continuity is proved separately by the corresponding
continuity rules. `Holomorphic.congr` transfers the construction to an
independently supplied equivalent evaluator on the same domain.

For a derivative value bounded by a positive rational \(B\), the unit-error
radius gives
\[
\|f(z)-f(a)\|_\infty\le (1+2B)H.
\]
`valueBound` reads \(B\) from the first valid box. Product remainders use
this bound on both increments, and the chain rule uses it to control the
outer increment. All choices are finite rational computations on supplied
data; no compactness, abstract completion, or Cauchy representation is used.
The radii can differ between equivalent representations; their derivative
values and mathematical laws agree.

## Polynomials and differential equations

`HolomorphicPolynomial` constructs polynomials with arbitrary represented
complex coefficients by finite sums and products. `ofCoefficients` agrees
literally with Horner evaluation, and `ofCoefficients_congr` proves
independence from both input and coefficient representations.

The formal expression `diff` is connected to the actual derivative by
`derivative_equiv` and `hasDerivative`. Every iterated `diff` is again a
holomorphic polynomial, and `iterated_hasDerivative` certifies each successive
step. In particular, `derivative_holomorphic` supplies the derivative-map
witness required by the continuation/ODE interface; it is no longer a
separate hand proof for every polynomial example.

For polynomial coefficients \(A,B,C\), `secondOrder_equiv` identifies the
computed polynomial expression
\[
A(z)p''(z)+B(z)p'(z)+C(z)p(z)
\]
with the existing `Continuation.secondOrderResidual` of actual derivatives.
The residual expression is holomorphic. Its vanishing is a separate equation
to prove, not an assumed field or an automatic consequence of holomorphicity.

## Function-theory audit and next direction

| Component | Checked scope | Remaining bridge |
| --- | --- | --- |
| Basic differential calculus | Continuity, sums, products, compositions, equivalent evaluators | Reciprocal and general rational-map constructor |
| Polynomials | Arbitrary represented coefficients and inputs; every iterated derivative; ODE residual comparison | General series cannot be inferred from finite polynomial proofs |
| Complex exponential and local logarithm | Existing rational-input series, jets, and finite secant estimates | Represented-input evaluators and `Holomorphic` witnesses |
| Polygonal Cauchy cancellation | Supplied effective local models and sampled quadrature | Uniform model construction from local derivative data and integral comparison |
| Cauchy–Taylor reconstruction | Supplied quantitative Cauchy representation at rational complex inputs | Cauchy formula from holomorphicity, represented inputs, and identification with derivatives |
| Continuation | Germs, derivative comparison, gluing, actual chart chains, finite transport | General identity theorem, arbitrary chain comparison, and analytic monodromy |
| Fuchs applications | Concrete entire solution and rational-ray growth comparison | General complex Frobenius branches, uniform ray/sector adapters, solution existence and uniqueness |

The basic algebraic calculus and polynomial derivative components are complete
at their stated scopes. **The full function-theory program is not complete.**
The next useful direction is a direct represented complex-series constructor:
reuse finite polynomial calculus, prove value and differentiated tails and a
local remainder estimate, and instantiate exponential and sine before general
Frobenius factors. This route does not require finishing the general Cauchy
formula first. Reciprocal neighborhoods then support rational functions and
the intended \(\sin(1/z)\) example. The Cauchy/identity-theorem route remains
a separate substantial task rather than a hidden assumption of these skills.

## Boundaries

This interface deliberately includes derivative continuity data. No theorem
equating it with bare pointwise classical holomorphicity is claimed. A
computable function need not be differentiable. Even when differentiable,
its derivative is not automatically supplied by the evaluator. A raw function
type does not establish Type-2 computability; executable concrete evaluators
and moduli must be preserved in constructions. Continuity is proved, not
assumed decidable.

The existing `HolomorphicJet` and `RepresentedHolomorphicJet` records remain
algebraic data. They have not all been upgraded into witnesses. Polynomial,
sum, product, and composition adapters are now checked.
Rational, logarithm, and exponential adapters remain further work. The
affine and square examples remain independent concrete witnesses.

In particular, the current pointwise moduli do not supply a uniform rectangle
mesh automatically. Derivative-to-contour constructors, whole-chunk integral
agreement, Cauchy's value and higher-derivative formulas, and a general
Cauchy-to-Taylor bridge retain their previous obligations. Rectangular grids
can be the working geometry without a universal contour-integral operator.

Run `lake env lean scripts/check_holomorphic.lean` after building
`ComputableAnalysis.HolomorphicPolynomial`. The audit checks the import
closure and proof dependencies, and
executes polynomial derivatives, a complex affine composition, and positive
error radii. It rejects unapproved axioms as well as unfinished proofs.
No Mathlib module or
`sorryAx` occurs. The printed dependency list includes inherited foundational
axioms, including an existing native-decision fact for positivity of one half;
this is not a claim of a newly axiom-free foundation.

The [holomorphic-functions skill](../skills/holomorphic-functions/SKILL.md)
contains the function-specific proof strategies.
