# Worked strategy test: normalized sine and power-series sine

The requested comparison has different coordinates. The primary
[normalized sine](../../../ComputableAnalysis/ElementaryRational.lean) takes
\(r\in\mathbb Q\) and computes \(\sin(\pi r)\). The primary
[power-series sine](../../../ComputableAnalysis/ElementaryPowerSeries.lean)
takes \(z\in\mathbb Q(i)\) and computes
\[
 S(z)=\sum_{n=0}^{\infty}\frac{(-1)^n z^{2n+1}}{(2n+1)!}.
\]
Its implementation pairs the odd terms of exponential prefixes; the checked
[coefficient identities](../../../ComputableAnalysis/ElementarySeriesCoefficients.lean)
justify this description. Comparing equal rational parameter numerals would
compare different angles. The intended real extension identity is
\[
 \widehat F(x)\simeq\widehat S(\pi x).
\]
Here the hats denote derived evaluation, not a change of the primary domains.

## Result for the actual implementations

**Finite prefix algebra and shrinking errors is the shortest checked route.**
The normalized computation already uses the exponential Taylor evaluator at
the represented angle \(\pi r\). It is not an independently constructed
geometric sine. The other computation separates the odd terms of that same
expansion. The
[real-axis comparison](../../../ComputableAnalysis/ElementarySeriesComparisons.lean)
proves exact agreement by exhibiting a common finite prefix in both output
enclosures. The
[exponential extension bridge](../../../ComputableAnalysis/ModularForms/ExponentialLiftAgreement.lean)
handles arbitrary valid represented arguments through rational centers and
shrinking input, truncation and output errors. Its representation invariance
is already available.

The concrete
[checked bridge](../../../ComputableAnalysis/ElementarySineComparison.lean)
adds the following results without a new evaluator:

- `powerSeries_rational_agrees_derived` identifies the real-axis primary
  power-series sine with the existing `sineAtAngle` add-on at every rational
  radian input.
- `sinPi_agrees_derived_powerSeries` identifies every primary normalized
  value with this add-on at \(\pi r\), including irrational physical angles.
- `sinPi_powerSeries_agrees_at_coordinates` compares the two primary
  functions wherever \(\pi r\simeq q\), retaining the exact coordinate
  premise rather than claiming their physical overlap is dense.

The first result transfers the established rational exponential construction
to the sine comparison. It is not a numerical spot check. Validity and
invariance of the angle operation are supplied by `sineAtAngle_valid` and
`sineAtAngle_congr`. The quantitative extension evidence is in the exponential
bridge. The completed ODE application below supplies a complex normalized
extension with explicit primary-function bridges and convergence.

## ODE uniqueness: the better characterization for independent constructions

For two independently constructed radian sine/cosine pairs, compare actual
solutions of
\[
 \frac{d}{dt}\begin{pmatrix}s\\c\end{pmatrix}
 =\begin{pmatrix}0&1\\-1&0\end{pmatrix}
   \begin{pmatrix}s\\c\end{pmatrix},
 \qquad (s(0),c(0))=(0,1).
\]
This first-order system avoids needing a separately packaged second
derivative. Equivalently, sine satisfies \(y''=-y\),
\(y(0)=0\), \(y'(0)=1\).

In the normalized coordinate, both aligned constructions must instead satisfy
\[
 f''=-\pi^2 f,\qquad f(0)=0,\qquad f'(0)=\pi.
\]
The first-order form is \(f'=\pi c\), \(c'=-\pi f\), with the same
initial pair. One must justify the derivatives and the coordinate chain rule;
initial values alone do not prove agreement.

The complete application is checked in
[`ElementarySineODESolutions`](../../../ComputableAnalysis/ElementarySineODESolutions.lean).
For every valid represented complex frequency \(a\), it constructs two actual
solutions of \(s'=ac\), \(c'=-as\), with initial pair \((0,1)\): the paired
scalar entire exponentials at \(iaz\) and \(-iaz\), and the independently
computed rotation-matrix Taylor sum. Holomorphicity, both derivative laws and
both initial values are proved from the constructions. The central
`computations_agree_global` proof compares them using those laws, rather than
using an existing sine identity.

[`EntireConstantODEUniqueness`](../../../ComputableAnalysis/RiemannHilbert/EntireConstantODEUniqueness.lean)
multiplies each solution by the actual inverse matrix exponential and proves
zero derivative. Checked local ODE uniqueness gives constancy neighborhoods;
the finite rational open-cover argument in `HolomorphicPathConstancy`
propagates constancy along the constructed affine path from the origin to
any endpoint. Entire-domain membership holds at every path parameter. No
small endpoint restriction, assumed uniqueness provider, caller-supplied
cover or assumed final comparison is required.

[`ElementarySineODEComparison`](../../../ComputableAnalysis/ElementarySineODEComparison.lean)
then proves, on the entire represented complex plane,
\[
 \widehat F(z)\simeq\widehat S(\pi z).
\]
The coefficient \(\pi\) is the repo's valid computed geometric pi, with no
rationality assumption. Matrix Taylor parameter scaling justifies the actual
coordinate change. Separate adapters connect the entire computations to the
primary normalized function on \(\mathbb Q\) and the primary power-series
function on \(\mathbb Q(i)\). For every prescribed positive rational error,
`powerSeries_primary_converges` and `sinPi_primary_converges` prove eventual
closeness of those primary values at computed rational centers/midpoints to
the derived value. Holomorphic continuity moduli and shrinking input-box
errors supply the schedules, so irrational evaluation is justified from the
primary computations.

The primary power-series adapter still uses the established finite
odd-prefix identity to identify its exponential formula, then the new ODE
proof to identify the matrix Taylor computation. Thus the ODE core is an
independent comparison route; this does not turn the existing normalized
implementation into an independently constructed geometric sine.

The older [`ScalarODEUniqueness`](../../../ComputableAnalysis/ScalarODEUniqueness.lean)
module is different: its self-derivative uniqueness provider is still a
conditional input. It is not a ready-made harmonic-oscillator uniqueness
theorem.

## Why the identity theorem is less helpful in this test

The identity theorem requires holomorphic extensions in a common coordinate
and an exact local seed. Agreement only at the origin is insufficient. The
physical sets \(\pi\mathbb Q\) and \(\mathbb Q\) have not supplied an
accumulating common set of agreed nonzero points.

An ODE can supply the missing seed through its initial-value uniqueness, or
through its recurrence determining every Taylor coefficient. A coefficient
argument additionally needs actual local analytic reconstruction. The finite
prefix route already proves the present concrete comparison, so adding
holomorphic identity propagation would not remove a proof obligation.

For a future independent geometric sine, prefer a shared ODE and initial
normalization when its derivative evidence is easiest to construct. Prefer
the identity theorem when exact accumulating-set agreement or a local
analytic identity is already available. This is a choice based on the
constructions, not a permanent ranking of the methods.

## Verification

```bash
lake build ComputableAnalysis
lake env lean scripts/check_elementary_sine_comparison.lean
lake env lean scripts/check_elementary_sine_ode_comparison.lean
lake env .lake/packages/checkdecls/.lake/build/bin/checkdecls blueprint/lean_decls
```

The ODE audit checks solution evidence, initial values, global uniqueness,
primary bridges and center convergence. It also checks the transitive proof
dependencies: the central comparison uses both solution laws, actual global
uniqueness and path constancy, and uses no elementary sine-agreement theorem.
The primary normalized comparison does use the central ODE theorem.

Checked on 2026-10-12: the full library build passed (5396 jobs), as did the
blueprint declaration audit. All sixteen ODE audit endpoints use only
`propext`, `Classical.choice` and `Quot.sound`. The transitive core proof audit
found both actual solution laws and initial values, the global uniqueness
law and checked path constancy; it found no earlier elementary sine agreement.
The applied primary comparison includes the central ODE theorem. No Mathlib,
Std or Batteries imports were found in the library. Skill metadata and relative
reference links passed validation.
