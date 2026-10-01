# Rational functions

Partial fractions suggest logarithms and arctangents, but a pole inside the interval can invalidate an endpoint calculation. The [worked page](../../../book/rational-primitives/index.html) motivates that distinction. Use this recipe to connect a supplied algebraic decomposition to actual function-specific integrals.

Start with the actual quotient and its domain. A supplied factorization is useful
input; finding a factorization is a separate problem. Read the
[shared formalization policy](../../../FORMALIZATION_GUIDE.md#computable-foundations-exact-mathematical-theorems)
and retain arbitrary valid represented coefficients and endpoints in the requested theorem.

## Construct the finite approximation

Certify a positive lower bound for the denominator's modulus on the entire
interval or path. Endpoint checks do not exclude an interior pole. Subdivide
until interval arithmetic proves separation; use a supplied separation bound
to justify termination rather than treating an unsuccessful search as a proof
of a pole.

On each real cell, enclose the quotient by rational lower and upper constants.
Their integrals are finite step-function sums. On a straight complex segment
with displacement \(\Delta z_i\), choose a constant \(c_i\) and prove
\(|f(z)-c_i|\le\varepsilon_i\) throughout the segment. Then use the elementary
value and the proposed comparison budget

\[
S=\sum_i c_i\Delta z_i,\qquad
E=\sum_i\varepsilon_i|\Delta z_i|.
\]

Construct the semantic comparison before using \(E\) as an integral error.
Directed real intervals or separate real and imaginary bounds turn it into
rational output boxes. A rational upper bound for each displacement's modulus
is sufficient; computing an exact length is unnecessary.

## Worked route: a quadratic denominator

For \(f(x)=1/(1+x^2)\) on \([0,1]\), let \(h=1/N\), with \(N\ge1\).
The function decreases, so the elementary lower and upper sums are

\[
L_N=h\sum_{k=1}^{N}\frac1{1+(kh)^2},\qquad
U_N=h\sum_{k=0}^{N-1}\frac1{1+(kh)^2}.
\]

Finite cancellation gives \(U_N-L_N=1/(2N)\). Dyadic refinement supplies nested
boxes. Prove their integral role from the whole-cell inequalities. Identification
with an arctangent endpoint difference is a further comparison theorem.

## Obtain a closed form without changing the problem

Use polynomial division and partial fractions when a factorization is supplied.
Handle repeated poles and quadratic factors explicitly. For each logarithm or
arctangent term, certify a branch over the full integration route. A loop may
cross local branch charts even though it avoids poles: transport the branch with
the [analytic-continuation skill](../../analytic-continuation/SKILL.md).

Prove the definite-integral identity with its base point and orientation.
A formal derivative of the generated expression is an intermediate result;
it does not certify the original integral. Do not ask callers for a certificate
whose content is the desired endpoint agreement.

## Proof sources and checks

Read [the rational-function progress report](../../../docs/RATIONAL_PRIMITIVES.md)
before choosing an existing bridge. It distinguishes finite partial fractions,
analytic atom certificates, and the still-incomplete general assembly.
[VerticalReciprocalIntegral](../../../ComputableAnalysis/VerticalReciprocalIntegral.lean)
is a direct complex range-box computation; raw validity alone is not a universal
path-integral theorem.

Audit the concrete result on its stated domain, including irrational inputs,
denominator separation, orientation, and representation invariance. Use the
[formalization skill](../../computable-analysis-formalization/SKILL.md) for the Lean
verification procedure. This skill describes a construction method; it adds no
new checked theorem by itself.
