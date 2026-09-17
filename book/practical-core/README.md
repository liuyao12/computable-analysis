# Exponential and logarithm: the next practical chapter

Status: source draft and audit, not a new published edition or a claim that
new Mathlib comparisons are complete. The existing mathematical proof source
is f630241adeae35fc06a5fd4921a4df6396e291d0. No original theorem or numerical
program is modified by this draft.

The narrative template in `chapter.html` organizes existing results into a
useful sequence: factorial evaluation; local derivative and growth; comparison
with repeated multiplication at one; the exponential integral on [0,1]; two
computations of log 2; and the square-substitution rational integral.

The longer exp/log manuscript remains unchanged. Its general addition and
inverse-law discussion is the next mathematical target, not something the
currently linked local derivative theorem establishes automatically.

## Reproduce the checked declarations and real executions

From the repository root, using the pinned Lean toolchain:

```sh
lake build ComputableAnalysis.ExpProofs ComputableAnalysis.Logarithm
lake env lean book/checks/ExportPracticalCore.lean
```

The exporter reads 43 existing declarations, checks five closed result roots
for transitive sorryAx, Mathlib and native-owned noncomputable dependencies,
and executes 21 finite evaluations of the actual Lean definitions. It writes
`practical-core-declarations.json` and `practical-core-examples.json`. Full
inherited axiom lists remain in the export; avoiding Mathlib is not a claim
that the logical foundation is axiom-free.

This export and the 21 computations ran locally with Lean 4.33.0-rc2. They are
not a new CI run. The numerical outputs were independently replayed using
exact rational finite arithmetic, without a Python exp/log evaluator.

For example, factorial-series stage 4 gives outward-rounded enclosures:

| Computation | Enclosure |
| --- | --- |
| E(-1) | [0.367879441148, 0.367879441173] |
| E(1/10) | [1.105170918075, 1.105170918076] |
| E(1) | [2.718281828434, 2.718281828460] |

These are rounded displays of exact rational endpoints, not interval output
from a floating-point special-function implementation.

## Remaining work before publication as a completed chapter

- Connect the supplied chapter template to theorem-side maps and quantitative
  comparisons without falsely treating existing native proofs as paired ones.
- Supply Mathlib representation bridges and proofs of the SAME native program
  propositions; no new paired comparison is currently completed.
- Complete logarithm on supplied positive rational intervals, exponential
  rules on arbitrary bounded intervals, and both inverse identities.
- Add range reduction, real powers and a constant-coefficient first-order ODE
  example, with actual numerical error estimates.

The chapter template retains the intended mathematical sequence. Numerical
tables are generated from the exporter, not hard-coded library values.
