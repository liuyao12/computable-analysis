---
name: real-integrals
description: Specify, construct, and compare integrals of real functions using the project's computable foundation, including finite intervals, improper endpoints, integral laws, and closed-form comparisons.
---

# Real integrals

Start with the function, its domain, and the requested integral law or value.
Each function brings its own construction and evidence. Read the
[formalization policy](../../FORMALIZATION_GUIDE.md#computable-foundations-exact-mathematical-theorems).
Use rational interval algorithms, arbitrary valid represented inputs, and
`RealRaw.Equiv` for exact equality. Do not import Mathlib's real numbers or
replace quantitative estimates by an abstract completion argument.

## Specify the integral before constructing it

Separate laws about supplied, justified integral objects from existence of a
particular computation. State linearity, orientation, interval addition, and
order or comparison inequalities with the evidence needed by each law. For
example, with justified integral witnesses and valid coefficients,

\[
I_a^b(\alpha f+\beta g)\simeq\alpha I_a^b(f)+\beta I_a^b(g),
\qquad I_a^c(f)\simeq I_a^b(f)+I_b^c(f).
\]

These are theorem obligations, not laws obtained by giving a record fields
with these names. Prove uniqueness from justified comparisons or common laws;
do not assume a uniqueness field. The current `Integral.HasIntegral` uses
arbitrarily tight rectangle tests: it is a checked sufficient route, not a
method-independent requirement for every integrand. Numerical candidate
validity does not establish the candidate's integral role.

## Recover the elementary integral

For step values on a finite partition, recover

\[
I_a^b(s)\simeq\sum_i c_i(x_{i+1}-x_i).
\]

Prove invariance under common refinement and changes at finitely many
breakpoints, together with orientation, linearity, and interval addition.
Constants and endpoints may be represented values. Finite rational cases are
useful tests, not the entire public domain. This elementary support does not
require every function to admit a particular step-approximation scheme.

## Compute with explicit lower and upper bounds

For the function at hand, justify whole-cell bounds, derivative estimates,
finite identities, or another comparison route. When using rectangles, prove
\(m_i\le f(x)\le M_i\) throughout each cell and form

\[
L_n=\sum_i m_i\Delta x_i,\qquad
U_n=\sum_i M_i\Delta x_i,\qquad U_n-L_n\le\varepsilon_n.
\]

Prove coverage, validity, nesting or justified stabilization, and an explicit
schedule making the error arbitrarily small. Budget evaluation errors as well
as subdivision errors. Point samples alone do not bound a cell. Prove the
semantic comparison between the computed value and the supplied integral laws.
For represented endpoints, control the endpoint brackets and prove independence
of their choices instead of silently narrowing the theorem to rational inputs.

For a closed form, establish the derivative's local finite inequalities on the
whole segment, then apply a justified FTC comparison to obtain
\(I_a^b(f)\simeq F(b)-F(a)\). Do not assume that endpoint identity to prove it.
A pole or branch check at the endpoints alone is insufficient.

## Handle an improper endpoint for this function

Choose a domain exhaustion and construct actual compact integral witnesses
first. At stage \(n\), combine their computation error with a justified tail
allowance. For a nonnegative tail bounded by \(T_n\), an enclosure
\([L_n,U_n]\) for the compact integral yields \([L_n,U_n+T_n]\); for a signed
tail with absolute bound \(T_n\), use \([L_n-T_n,U_n+T_n]\).

Estimate differences of finite truncations before assuming an improper value
exists. Prove convergence with an explicit joint schedule and justify the
exhaustion's domain interpretation. Independence of other exhaustions is a
comparison theorem. For divergence, prove a quantitative obstruction using
actual finite truncations; failure of an estimate does not prove divergence.

## Examples by function

Read only the relevant construction reference:

- [Rational functions](references/rational-function-integrals.md): whole-domain pole separation and closed-form comparisons.
- [Trigonometric functions](references/trigonometric-integrals.md): circle-coordinate bounds and turning-point brackets.
- [Powers and improper endpoints](references/improper-power-integrals.md): compact witnesses, endpoint estimates, and subsequent series comparison.
- [Gaussian and Gamma integrals](references/gaussian-gamma-integrals.md): separate finite errors, tails, normalization, and geometry.

Use the [series skill](../series/SKILL.md) for infinite sums. To avoid circularity
in an integral test, first prove finite integral identities and finite
sum–integral inequalities, then derive the series result.

## Proof sources and checks

Read [IntegralRectangleSpecification](../../ComputableAnalysis/IntegralRectangleSpecification.lean)
for the checked rectangle specification and its scoped uniqueness theorem,
and the example's own proof-status report before claiming existence or a
closed form. Follow the [formalization skill](../computable-analysis-formalization/SKILL.md)
for theorem audits. This guide adds no Lean theorems; existing candidate APIs
must not be promoted to integral specifications by their names alone.
