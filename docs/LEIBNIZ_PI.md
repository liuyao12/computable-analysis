# Leibniz computation of geometric π

The canonical object remains `ComputableAnalysis.piCircleArea`, whose stages
are exactly four times the geometric arctangent at one. No new π is defined.

Import `ComputableAnalysis.LeibnizPi` for the public computational theorem,
or `ComputableAnalysis.LeibnizPiTaylor` for both proofs. The benchmark remains
opt-in, consistent with the canonical root’s treatment of worked examples.
The blueprint target imports both proofs for declaration verification.

New Lean modules:

- `AlternatingRemainder`: arbitrary-prefix first-omitted-term bounds for any
  `Series.AlternatingRaw`, including exact raw-order bounds.
- `FiniteSecantIntegralOrder`: quantitative finite differences imply exact
  integral order on rational subintervals of `[0,1]`. Its proof bisects cells
  finitely and uses the existing explicit `halfDecayShift` error schedule.
- `ArctanTaylorRemainder`: finite geometric identity, power remainder bound,
  actual normalized-monomial primitive certificates, and all-degree integral order.
- `LeibnizPi`: inclusive rational partial sums, the existing alternating
  interval construction scaled by four, convergence, and the computational proof.
- `LeibnizPiTaylor`: the independent FTC proof and the integrated remainder.

## Public statements

All names below are in namespace `ComputableAnalysis`.

- `pi_eq_leibniz : piCircleArea.Equiv leibnizRaw`
- `pi_eq_leibniz_taylor : piCircleArea.Equiv leibnizRaw`
- `leibnizPartial_succ` identifies the literal signed rational summands.
- `leibnizRaw_valid` and `leibnizRaw_width_le` certify the computation.
- `leibniz_stagewise_overlap` gives both requested inequalities for every `N`.
- `pi_leibniz_remainder` states `S_N - 4/(2N+3) ≤ π ≤ S_N + 4/(2N+3)`
  using `RealRaw.Le`.
- `arctan_taylor_integrated` and `arctan_taylor_remainder_bound` give the
  finite integrated formula and `-1/(2N+3) ≤ R_N ≤ 1/(2N+3)`.

The inclusive index `N` in the mathematical sum is independent of the raw
approximation stage. At runtime stage `n`, the evaluator uses the interval
between the prefixes with `2n` and `2n+1` terms. This is proved equal to the
existing fold-based `piLeibniz` evaluator, including stage zero. Thus the new
interface reuses the existing algorithm as well as the existing geometric π.

## Dependency paths

The computational closure reaches
`PiProofs.leibnizEqualsRectangleRawAtOne_finiteRiemannBridge`: finite kernel
polynomial rectangle estimates, an explicitly scheduled rational mesh,
vanishing error intervals, and geometric exhaustion. No derivative or FTC
certificate is used on this path. Arithmetic lemmas housed in `FTC` and finite
monomial algebra housed in `Taylor` are still shared dependencies.

The second closure reaches
`Taylor.ArctanKernel.kernelPartial_exactCellOrder`, through
`kernelPrimitiveSecantBound`, normalized-monomial finite differences, and
`FinitePolynomial.SecantDerivativeBound.exactCellOrder`. The existing
`PiProofs.leibnizEqArea_of_kernelPartialExactCellOrderPreservation` then
integrates the geometric-series bounds and compares the rectangles with geometry.
It does not call the computational finite-Riemann bridge. Both proofs share
rational arithmetic, raw-real validity/order, finite geometric algebra, and the
geometric rectangle/exhaustion comparison.

`PiProofs` also uses the new all-degree certificate to replace its expensive
stage-12 and stage-15 numerical checkpoint proofs. Their statements and all
runtime evaluators remain unchanged. The publication baseline also needed two
pre-existing build fixes: removing a redundant interval-negation `unfold` and
turning orphaned docstrings into ordinary comments; no theorem or evaluator
statement is changed by those fixes.

The modules have overlapping import closures because `PiProofs` is an existing
presentation module. Proof independence is checked on elaborated declaration
dependencies, not inferred from imports or theorem names. Existing geometric
proofs carry native-decision dependencies; the new proof modules add none.

## Verification

```sh
lake build ComputableAnalysis.LeibnizPiTaylor
lake env lean scripts/check_leibniz.lean
lake build ComputableAnalysis ComputableAnalysisBlueprint checkdecls
lake env .lake/packages/checkdecls/.lake/build/bin/checkdecls blueprint/lean_decls
python3 blueprint/checks/check_foundation_imports.py
python3 blueprint/checks/check_special_function_identities.py
```

The focused script checks both positive and negative dependency reachability,
rejects `sorryAx`, prints axiom reports, and evaluates small exact stages. The
complete transitive project-declaration closures are written to
`tmp/leibniz-dependency-closure.txt`; the reader publication preserves that report.
The public source-import closure contains only project modules and
`Init.Grind.Ordered.Rat`, with no Mathlib dependency.

The reader publication adds a dependency note and a linked interactive mathematical
map of the two native proofs and Mathlib’s Abel-limit proof. Its 17 source-linked
bundles emphasize mathematical arguments, with route filters and an accessible
reading outline. Arrows summarize dependencies across intermediate lemmas; this
curated graph is distinct from the complete elaborated native declaration audit.
The Mathlib sources are pinned to `338b8c00bd151fa07a0350cc17442e6eeda734e8`. It retains the pinned manuscript, cosine, Cartwright, Wallis,
beta, theorem-map data, and existing pages, and identifies the new proof source
separately. The graph changes the reader presentation only; it adds no new Lean theorem
or translation between the native and Mathlib π objects.
