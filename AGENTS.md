# Repository guidelines

## Pedagogical exposition

Treat the project as a book for learning mathematics. Each reader page should
make clear what question it answers and why the next construction is useful.
Begin with a concrete example, puzzle, application or obstruction before
introducing the technical contract. If an earlier chapter or section already
supplies the motivation, refer to that specific discussion and explain the
new step instead of repeating it.

Let discovery order guide the narrative: a plausible strategy and its limits
can precede a cleaner proof that takes a different route. Explain why the
hypotheses matter using examples or counterexamples when helpful. At major
transitions, connect the next estimate or definition to the problem it solves.
Keep source inventories and proof-status detail available after the mathematical
story, while accurately distinguishing checked results from targets.

Maintain the page review and narrative additions in `book/pedagogy/pages.json`;
new reader pages must be included in its coverage check. Preserve exact theorem
statements, genuine domain and branch restrictions, formulas, computation data
and proof links when revising the prose. See `docs/PEDAGOGICAL_EXPOSITION.md`.

## Integral and series skills

For constructions, use the [real-integral skill](skills/real-integrals/SKILL.md),
[complex-path-integral skill](skills/complex-path-integrals/SKILL.md), or
[series skill](skills/series/SKILL.md) before the general formalization workflow.
The reader showcases these three guides after the chapters. Particular-function
recipes are supporting examples within the guides.

Piecewise-constant functions on piecewise-linear paths are the common
elementary baseline. Every proposed integration theory must recover their
finite sum of constants times displacements, with subdivision and finite
breakpoint-value invariance. This does not require every other integrand to
be constructed by a particular approximation scheme.

## Computable foundations and exact theorems

Read [the governing formalization policy](FORMALIZATION_GUIDE.md#computable-foundations-exact-mathematical-theorems)
and the [formalization skill](skills/computable-analysis-formalization/SKILL.md)
when adding or reviewing mathematics.

- Prefer general laws about supplied, justified constructions. Prove their
  consequences from explicit validity, domain, convergence, derivative, or
  solution evidence; broad existence criteria are a separate task. A proved
  conditional law is complete at its stated scope. For a requested concrete
  example, construct its evidence. Do not assume the desired conclusion inside
  a record and advertise its projection as a new mathematical theorem.
- Keep the foundation computable: rational interval algorithms, validity
  proofs, explicit errors, bounds, and convergence schedules. Do not use
  Mathlib's real numbers or abstract completion shortcuts.
- State public mathematical theorems as exact identities over valid represented
  reals, using `RealRaw.Equiv` for equality of values. Quantify over arbitrary
  valid represented inputs and coefficients, including irrational ones.
  Preserve executable algorithms for executable inputs; a raw function type
  alone is not a computability certificate. Prove representation invariance.
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
