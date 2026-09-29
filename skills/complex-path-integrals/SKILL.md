---
name: complex-path-integrals
description: Specify and compute integrals of complex functions along paths or loops, starting with piecewise-linear geometry and justified linearity, concatenation, orientation, and error comparisons.
---

# Complex path integrals

Specify the function, oriented path, and its entire domain before choosing a
computation. Follow the [formalization policy](../../FORMALIZATION_GUIDE.md#computable-foundations-exact-mathematical-theorems).
Use represented complex values built from the project's real computations,
rational rectangles, and `ComplexRaw.Equiv`. No Mathlib real or complex
completion is needed. Existence for a particular function is separate from
laws about supplied, justified integrals.

## Start with the elementary path computation

For a continuous polygonal path, subdivide at both vertices and integrand
jumps. A constant value \(c_i\) on each open piece gives

\[
I_\gamma(s)\simeq\sum_i c_i(z_{i+1}-z_i).
\]

Prove common-refinement invariance, independence of finitely many breakpoint
values, reversal, and concatenation by finite algebra. Allow arbitrary valid
represented vertices and constants; exact rational geometry is a useful
executable case. A trace that assigns different values on repeated visits is
path data and need not come from a single-valued function on the plane.

## State and justify the integral laws

For compatible supplied integral witnesses, prove

\[
I_\gamma(\alpha f+\beta g)\simeq\alpha I_\gamma(f)+\beta I_\gamma(g),
\qquad I_{\gamma*\eta}(f)\simeq I_\gamma(f)+I_\eta(f),
\qquad I_{\gamma^{-1}}(f)\simeq-I_\gamma(f).
\]

Concatenation requires matching path endpoints and valid function data along
both paths. Linearity requires evidence for the integrals involved. These
laws and the elementary baseline do not by themselves establish uniqueness
for arbitrary integrands: prove the needed comparison or approximation result.
Do not encode the desired conclusion as an assumed record field.

For a whole-piece estimate \(|f(z)-c_i|\le\varepsilon_i\), justify the bound

\[
\left|I_\gamma(f)-\sum_i c_i\Delta z_i\right|
\le\sum_i\varepsilon_i|\Delta z_i|.
\]

A rational upper bound for each displacement length is enough for an error
budget. This is one sufficient route, not a mandatory definition of all
integrals. For more general paths, supply additional path-control and
comparison evidence; polygonal computations alone do not settle their existence.

## Compute rectangles and prove their meaning

Enclose the function over each entire geometric segment, multiply the value
rectangle by the oriented displacement, and add. Complex multiplication
rotates and mixes coordinates; multiplying separate lower endpoints is not
sound. Prove rectangle containment, a shrinking width schedule, and validity
or justified stabilization. Include errors in represented vertices and
constants. Then prove agreement with the justified integral specification.

A parameter pullback offers another route, provided the relation to the path
and its differential is proved. For \(\gamma=x+iy\) and \(f\circ\gamma=u+iv\),
the two real integrands are

\[
\operatorname{Re}\bigl((f\circ\gamma)\gamma'\bigr)=ux'-vy',
\qquad
\operatorname{Im}\bigl((f\circ\gamma)\gamma'\bigr)=uy'+vx'.
\]

Use the [real-integral skill](../real-integrals/SKILL.md) for those components
and prove reparametrization agreement under the supplied hypotheses. A valid
pair of component computations does not by itself justify the path relation.

## Closed forms and loops

Certify pole avoidance and branches along every segment. A locally defined
logarithm can change branch after continuation around a loop; equal geometric
endpoints alone do not prove zero integral. Use the
[analytic-continuation skill](../analytic-continuation/SKILL.md) when charts
are needed. Prove finite cancellation and vanishing error estimates before
claiming Cauchy, deformation, or endpoint theorems.

The [rational-function example](../real-integrals/references/rational-function-integrals.md)
illustrates pole separation. The [polygonal Cauchy reader](../../docs/POLYGONAL_CAUCHY.md)
records the actual checked scope and open analytic bridges.

## Proof sources and checks

Read [ComplexPathIntegral](../../ComputableAnalysis/ComplexPathIntegral.lean),
[ComplexIntegralEnclosure](../../ComputableAnalysis/ComplexIntegralEnclosure.lean),
and [FiniteComplexPathCertificate](../../ComputableAnalysis/FiniteComplexPathCertificate.lean)
for finite computations, soundness, and validity at their stated scope. Use
[the formalization skill](../computable-analysis-formalization/SKILL.md) for
verification. These modules and this guide do not establish every abstract
path-integral law; retain the distinction between a numerical candidate and
a proved integral witness.
