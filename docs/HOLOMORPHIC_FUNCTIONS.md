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

## Boundaries

This interface deliberately includes derivative continuity data. No theorem
equating it with bare pointwise classical holomorphicity is claimed. A
computable function need not be differentiable. Even when differentiable,
its derivative is not automatically supplied by the evaluator. A raw function
type does not establish Type-2 computability; executable concrete evaluators
and moduli must be preserved in constructions. Continuity is proved, not
assumed decidable.

The existing `HolomorphicJet` and `RepresentedHolomorphicJet` records remain
algebraic data. They have not all been upgraded into witnesses. Generic
polynomial, rational, logarithm, exponential, sum, product, and composition
adapters are further work. The affine and square examples are fully
instantiated at represented inputs.

In particular, the current pointwise moduli do not supply a uniform rectangle
mesh automatically. Derivative-to-contour constructors, whole-chunk integral
agreement, Cauchy's value and higher-derivative formulas, and a general
Cauchy-to-Taylor bridge retain their previous obligations. Rectangular grids
can be the working geometry without a universal contour-integral operator.

Run `lake env lean scripts/check_holomorphic.lean` after building the example
module. The audit checks the import closure and proof dependencies, and
executes the square evaluator and radius computation. No Mathlib module or
`sorryAx` occurs. The printed dependency list includes inherited foundational
axioms, including an existing native-decision fact for positivity of one half;
this is not a claim of a newly axiom-free foundation.

The [holomorphic-functions skill](../skills/holomorphic-functions/SKILL.md)
contains the function-specific proof strategies.
