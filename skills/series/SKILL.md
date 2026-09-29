---
name: series
description: Define, compute, and compare sums of real or complex series through ordered finite partial sums, explicit tail estimates, convergence schedules, and quantitative divergence witnesses.
---

# Series

Specify the terms, starting index, and order of summation. Define what it
means for a supplied valid represented value to be their sum before proving
that this particular series has one. Follow the
[formalization policy](../../FORMALIZATION_GUIDE.md#computable-foundations-exact-mathematical-theorems);
use project interval computations rather than Mathlib reals or abstract completion.

## Define the mathematical claim

For the ordered prefixes \(S_N=\sum_{k=0}^{N-1}a_k\), a supplied value \(S\)
is a sum when the prefixes converge to it:

\[
\forall\varepsilon\in\mathbb Q_{>0}\;\exists N\;
\forall M\ge N,\quad |S_M-S|\le\varepsilon.
\]

This specifies a property, not a universal summation algorithm. Prove
uniqueness by comparing late prefixes. Keep existence of a limit separate
from an executable constructor with an explicit index schedule. Preserve
arbitrary valid represented inputs and representation invariance in exact
public theorems; equality means `RealRaw.Equiv` or `ComplexRaw.Equiv`.

## Compute without assuming the infinite sum

Prove finite future-prefix bounds

\[
|S_M-S_N|\le E_N\qquad(M\ge N),
\]

with nonnegative rational errors and an explicit schedule making them small.
For rational terms, use candidate boxes \([S_N-E_N,S_N+E_N]\). Prove nesting
or justify finite intersections or stabilization; these symmetric boxes are
not automatically nested. Prove nonemptiness as well as a shrinking width.
Then prove that the resulting represented value satisfies the sum property.

For represented terms, compute a finite prefix enclosure \([L_N,U_N]\)
and add the tail allowance. Choose term precisions so that accumulated
rounding error plus truncation error fits the requested tolerance. For complex
terms use coordinate bounds and rational rectangles. Bounded increasing
prefixes alone do not supply an executable convergence schedule.

## Choose estimates from the terms

Use alternating brackets, geometric ratios, finite telescoping, factorial
ratio bounds, or another proved estimate for the specific terms. Do not make
absolute convergence mandatory for an ordered conditionally convergent sum.
Read [series computation strategies](../computable-analysis-formalization/references/series-computation-strategies.md)
for the available routes and their hypotheses.

For example, if \(|q|\le r<1\), finite geometric algebra yields

\[
\left|\sum_{k=N}^{M-1}q^k\right|\le\frac{r^N}{1-r}.
\]

Choose the cutoff from this rational majorant. The finite identity
\((1-q)S_N=1-q^N\), together with a vanishing remainder and certified
nonzero denominator, identifies the sum with \(1/(1-q)\). Keep construction
and closed-form identification as separate proofs.

## Prove laws and divergence with their evidence

Linearity follows from finite-prefix identities and combined convergence
budgets for supplied sums. Acceleration, regrouping, products, permutations,
termwise integration, and differentiation need additional finite comparisons
and appropriate remainder control. Conditional convergence alone does not
permit arbitrary permutations.

For divergence, give a quantitative obstruction for the actual prefixes:
for example, a fixed positive separation between arbitrarily late prefixes,
or a failure of the terms to tend to zero. Failure to find a tail estimate is
not evidence of divergence.

For an integral test, use the [real-integral skill](../real-integrals/SKILL.md)
and the [power example](../real-integrals/references/improper-power-integrals.md).
Prove finite sum–integral inequalities and independently justified compact
integrals before deriving the infinite-series claim, avoiding circular use of
that same series to justify the integral.

## Proof sources and checks

Read [Series](../../ComputableAnalysis/Series.lean),
[SeriesFoundation](../../ComputableAnalysis/SeriesFoundation.lean), and
[PowerSeries](../../ComputableAnalysis/PowerSeries.lean) for checked finite
lemmas and sufficient construction packages. `RationalSeriesCertificate` is
one nested-interval route, not the definition of every sum. Consult the
[formalization skill](../computable-analysis-formalization/SKILL.md) for audits.
This skill adds no new Lean convergence or closed-form theorem by itself.
