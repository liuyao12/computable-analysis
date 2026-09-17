# Weighted cosine moments: complete paired formalization

Native entry point: `ComputableAnalysis.Cartwright`.
Optional comparison entry point: `MathlibComparison.Cartwright`.
Lean 4.33.0-rc2; Mathlib pinned by the existing comparison package.

## Exact common objects and statements

`CartwrightMoments.moment n` is an independent finite rational computation of
J_n = integral_0^1 (1-t*t)^n C(t/2) dt. At stage k it uses a dyadic mesh of depth
k and sample stage k, a proved radius 113/2^k, finite-prefix stabilization, and
intersection with [0,1]. `moment_valid` and `moment_width` prove validity and
width <= 226/2^k without the evaluation or an assumed primitive.

The cosine samples are rational circle coordinates of the existing closed
inverse-arctangent computation. Their uniform evaluation difference bound is
56(2^-q + 2^-r), and their finite mesh error is <= 2^-d. Multiplying by the
polynomial weight in [0,1] preserves these bounds uniformly in n. No native
integrability predicate, noncomputable selection of a schedule, or arbitrary
pointwise diagonal argument is introduced.

The geometric pi stays literally four times geometric arctangent at one.
`frequency` is pi/2. `EvaluationStatement n` compares independently computed
lambda^(2n+1) J_n with 2^n*n! times the interval-polynomial recurrence evaluated
at lambda squared. `PiSquaredStatement` says the square of that same geometric
pi program is not equivalent to any constant rational program.

## Alternative routes and shared mathematics

- Finite: exact discrete summation by parts, local increment replacements and
  quadratic cross-increment bounds. It does not call the general FTC, its
  `finite_telescope` lemma, or the composite primitive model.
- FTC: quantitative product differentiation supplies one polynomial-trigonometric
  primitive; `chosen_samples_FTC` and endpoint estimates give the moment laws.
  This is not an unsupported claim that the composite primitive is concave.
- Mathlib: an independent monotone-quadrature bridge identifies the SAME native
  moment programs with real interval integrals. Mathlib FTC and two integrations
  by parts give the laws. No native moment evaluation and no existing pi
  irrationality or transcendence theorem is imported into this route.

All three inhabit the same `MomentLaws` proposition, with closed named proofs.
The common finite recurrence induction yields `EvaluationStatement n`. The
common denominator-clearing and rational-sample argument yields positive small
integers under a hypothetical rational squared frequency. `CartwrightArithmetic`
then uses the explicit witness N=2*a*a and a finite factorial estimate to finish.
The arithmetic constructor and obstruction have no integral or computed-real
dependencies. The instantiated final proofs of course retain their analytic
prerequisites.

The native routes share local estimates and finite arithmetic; their independence
means absence of cross-use of final proofs or the forbidden global FTC route,
not entirely disjoint mathematics. `MomentLaws` is an intermediate interface,
not a remaining caller obligation in any of the exported final theorems.

## Reproduce verification

```sh
lake build ComputableAnalysis.Cartwright
cd comparison
lake build MathlibComparison.Cartwright
lake env lean checks/ExportCartwright.lean
```

The exporter checks all nine theorem types (three analytic-law proofs, three
uniform moment evaluations, three complete irrationality proofs), no admitted
proof, native Mathlib/noncomputability boundaries, numerical definition
independence, and independence of validity/positivity from the evaluation.
It also rejects ready-made irrationality results on the comparison route.
Compiled smoke evaluations exercise the actual moment algorithm.

## Book and measurements

Run `book/complete_cartwright.py` after the existing book pipeline and export.
It replaces the arithmetic-only plan with completed moment and irrationality
maps, while preserving the old cosine graphs, dyadic demonstration and measured
cosine data. `thm:cartwright-plan` remains an alias for the completed application.
Each arrow is witnessed by stored declaration references. Statement arrows
unfold definitions only; proof arrows enter proof bodies.

The comparison measures full closures, cost beyond the statement, route-specific
cost beyond shared prerequisites, and incremental cost after the corresponding
previous cosine proof plus common arithmetic. The latter uses explicitly
route-specific baselines. Source LOC unions available declaration ranges,
excludes comments and blanks, and exposes coverage. It is not a count of every
compiled expression, a runtime measurement, or a proof of conceptual minimality.
Native-computation axioms inherited from the earlier foundation are reported,
not hidden behind a claim of kernel-only arithmetic checking.
