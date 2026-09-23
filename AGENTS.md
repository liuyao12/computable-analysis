# Repository guidelines

## Computable foundations and exact theorems

Read [the governing formalization policy](FORMALIZATION_GUIDE.md#computable-foundations-exact-mathematical-theorems)
and the [formalization skill](skills/computable-analysis-formalization/SKILL.md)
when adding or reviewing mathematics.

- Keep the foundation computable: rational interval algorithms, validity
  proofs, explicit errors, bounds, and convergence schedules. Do not use
  Mathlib's real numbers or abstract completion shortcuts.
- State public mathematical theorems as exact identities over valid represented
  reals, using `RealRaw.Equiv` for equality of values. Support computable
  irrational inputs and coefficients. Prove representation invariance.
- Construct and package quantitative proof data beneath the exact theorem.
  Keep estimates available, but do not require callers to choose internal
  precision schedules, monotone partitions, turning-point brackets, or charts.
  Prove the agreement results needed to hide those choices.
- Preserve the full mathematical domain. In particular, a global elementary
  derivative identity should apply to every valid represented real in its
  domain, without asking for monotonicity breaks. Keep genuine domain, pole,
  branch, and constructive existence hypotheses when necessary.
- State closed-form integration results as definite-integral identities
  \(\int_a^x f(t)\,dt \simeq F(x)-F(a)\), or as a base-point-normalized
  expression at \(x\). Do not introduce a separate formal notion of primitive
  or indefinite integral. Certify the entire segment between the endpoints:
  the formula must not cross a singularity, and endpoint checks alone do not
  suffice. A derivative identity is an intermediate step for this task.
- Finite estimates, formal differentiation, rational-input identities, and
  uninstantiated certificate interfaces are intermediate results when an exact
  real-input theorem is requested. Prove the connecting lemmas before claiming
  completion; do not assume them or silently narrow the requested theorem.
