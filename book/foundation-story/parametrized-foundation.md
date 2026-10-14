# Parametrized enclosures for limits, continuity, and derivatives

The mathematical role is certified by a covered valid diagonal. For rational
interval data \(Q_{n,m}\), choose cofinal index maps \(n(k)\) and \(m(k)\) and form

\[
C_k=Q_{n(k),m(k)}.
\]

The selected intervals must be ordered, nested, and arbitrarily narrow:
they form a valid `RealRaw`. Neither index has a prescribed speed. Coverage
is essential: a diagonal must enclose every observation at its selected input
resolution, rather than just selected samples. The represented output is
compared using `RealRaw.Equiv`; different box programs need not be identical.

## Preferred constructions: endpoint and secant bounds

Use known monotonicity, convexity, or concavity first. The covered-diagonal
specification justifies and compares the resulting constructions; concrete
proofs should expose the simpler bounds that make it apply.

For a nondecreasing function and rational brackets around the point,

\[
a_n\leq t\leq b_n\quad\Longrightarrow\quad
f(a_n)\leq f(t)\leq f(b_n).
\]

Continuity is checked by collapse of these endpoint bounds. For represented
endpoint values, use the rational box

\[
[\underline f_m(a_n),\overline f_m(b_n)]
\]

and prove its width shrinks along a supplied refinement schedule. Reverse
the endpoint roles for a nonincreasing function. Exact rational-valued
monotone functions automatically give ordered, nested endpoint image boxes
from nested input brackets. Represented endpoint boxes may need the checked
finite-prefix intersection construction to obtain nesting. Keep the whole
neighborhood covered and clip to the actual domain at boundary points.

For convexity, two outer secants bound all sufficiently nearby inner secants:

\[
S_f(l_n,u_n)\leq S_f(s,t)\leq S_f(v_n,r_n),
\qquad l_n<u_n<s<t<v_n<r_n.
\]

Differentiability is checked by collapse of the slope bounds, with endpoint
evaluation errors refined as needed. Concavity reverses their order. Reuse
the checked finite inequalities and convex semantic bridge, constructing any
missing concave transport or comparison proof for the supplied computation.
Monotonicity gives containment, not continuity by itself; curvature gives
slope order, not differentiability at a corner. Local construction choices
stay beneath the exact theorem on its full intended domain.

## Shared exact specification

`RawLimit.HasEnclosureValue tests c` requires a valid represented target and
some covered cofinal valid diagonal equivalent to it. The predicate `tests`
describes the observations at each input resolution. Its mathematical
interpretation comes from the application, not from the name of a record.
For decreasing, inhabited observation sets, `HasEnclosureValue.unique` proves
that any two outputs agree. It compares arbitrary supplied diagonals using
one valid common observation. It assumes neither an output equality nor a
canonical constructor.

`RawLimit.prefixRaw` performs finite rational prefix intersections.
`prefix_valid` proves its validity from shrinking output bounds, decreasing
observation sets, and valid common observations. No previously constructed
extension or completeness principle is needed. `prefix_hasEnclosureValue`
certifies the actual computation. Supplied executable stage schedules stay
executable. The logical existence adapters that use `Classical.choose` are
not advertised as executable stage selectors.

## Limits

For a sequence, observations are **every remaining term**:

\[
\mathrm{tests}(N)=\{u_j:j\ge N\}.
\]

`RawLimit.HasParametrizedLimit` uses that coverage. `parametrizedLimit_iff`
proves exact equivalence with `RawLimit.TendsTo`, the earlier target-box
presentation. A selected diagonal cannot skip unfavorable terms: the checked
`alternating_no_parametrizedLimit` rejects an alternating sequence even though
it has valid constant subsequences. Independent refinement of raw rows need
not work uniformly; the selected parametrization carries the precision choices.

## Continuity

`BracketContinuity.HasContinuousAt domain f x c` keeps
\(f:\mathbb Q\to\mathrm{RealRaw}\) primary. Every admissible valid input
bracket \(A\simeq x\) must have a covered valid output diagonal representing
\(c\). The observations at stage \(n\) are **all rational values throughout**
\([A_n.\mathrm{lo},A_n.\mathrm{hi}]\). Endpoint hulls alone do not suffice.
Admissibility retains the existing domain-contained, strictly positive-width
bracket convention, and the bracket family must be inhabited. This scope
covers nondegenerate intervals and their endpoints; no claim is made here
about arbitrary domains that have no admissible intervals.

Uniqueness, input/output/function representation invariance, agreement of
independently constructed bracket values, and agreement with existing values
at rational inputs are proved. Every rational sample remaining inside the
shrinking input brackets has the same limit. `hasContinuousAt_iff_neighborhoods`
proves the equivalent whole-bracket target-box property.

`IntervalRegularOn`, `ScheduledIntervalRegularOn`, and
`EpsilonDeltaContinuousOn` remain quantitative sufficient evidence. Their
new adapters construct the covered diagonal. They are not compulsory proof
methods for every continuous function. The scheduled constructor takes an
explicit input-stage schedule and certifies its literal finite intersections.
`continuousAt_closed` constructs the admissible brackets internally for every
valid represented input in a nondegenerate closed interval, including endpoints.

Concrete checks cover identity and constants with arbitrary represented
values, the old square interval evaluator, and a jump whose whole-neighborhood
images cannot shrink.

## Derivatives and preserved calculus

`BracketDerivative.HasDerivativeAt` now directly uses
`HasParametrizedLimit` for the secants of **every** admissible input bracket.
Each covered diagonal bounds the complete remaining secant tail.
`hasDerivative_iff_secantLimits` proves exact equivalence with the previous
pointwise derivative relation. Existing convex constructions, arbitrary
represented square inputs, represented affine coefficients, and closed-domain
endpoint examples therefore retain their checked scope.

The older `HasDerivativeOnInterval` is finite-difference evidence.
`toParametrizedDerivative` supplies its semantic bridge when its step radii
are genuinely positive and its derivative evaluator satisfies the new
continuity specification at the point. Neither hypothesis assumes the desired
derivative identity. The concrete exact affine certificate instantiates this
bridge. A legacy precision value of zero would allow no nonzero step, so
positivity must not be silently inferred from the old record's type.

The existing FTC, integral, series, and ODE laws retain their explicit
mathematical evidence. This migration does not assert a new FTC theorem from
bare pointwise differentiation. The integral's scope policy remains unchanged.

## Complex downstream interfaces

`ParametrizedComplexContinuity` proves covered valid coordinate-diagonal
adapters for both `FunctionTheory` and the domain-evidence interface used by
modular and Riemann--Hilbert work. Their continuity moduli cover **all complex
neighbors**, and their derivative estimates supply normalized remainder
coordinate enclosures converging to exact zero:

\[
\frac{f(z)-f(a)-d(z-a)}{H},
\qquad 0<H,\qquad \|z-a\|_\infty\le H.
\]

The existing complex certificates remain stronger quantitative evidence.
No opposite-corner directional secant criterion is substituted, no branch or
pole hypothesis is dropped, and no weakest-definition equivalence is claimed.

## Verification

The full-workspace build below checks the existing downstream library. The
[reader source bundle](https://liuyao12.github.io/computable-analysis/foundation-story/proof.tar.gz)
is a self-contained snapshot of the modules needed by the advertised proofs,
with a synthetic library root. After extracting it, run `lake build` and the
three packaged theorem audits. The blueprint declaration check applies to the
full workspace; the snapshot does not include the entire downstream library
or the blueprint. Its manifest identifies every source file by hash.

```sh
lake build ComputableAnalysis
lake env lean scripts/check_parametrized_foundation.lean
lake env lean scripts/check_bracket_derivative.lean
lake env .lake/packages/checkdecls/.lake/build/bin/checkdecls blueprint/lean_decls
```

The new theorem audit checks every advertised bridge and regression, rejects
nonstandard axioms and transitive Mathlib imports, and retains the older
bracket audit. The full library build checks the downstream dependencies.

## Holomorphic semantic core

The all-direction complex extension is now checked in
[HOLOMORPHIC_ENCLOSURES.md](HOLOMORPHIC_ENCLOSURES.md). Covered normalized
remainders are equivalent to the actual first-order estimate. Holomorphicity
now requires shrinking covered boxes for all nearby two-point complex secants
on an open domain. Derivative continuity is proved from this condition, which
is exactly equivalent to the previous continuous-derivative definition. The weaker pointwise property is retained separately. Checked calculus, whole-segment constancy, elementary and
full-disk special-function examples, and a conjugation rejection test exercise
this definition. The equivalent quantitative construction packages now supply proved Cauchy
formulae, exact local Taylor reconstruction, and constructed higher derivatives.
