# Comparison package instructions

Mathlib imports are explicitly permitted in this directory. The prohibition
on Mathlib imports in the native formalization guide applies to the independent
`ComputableAnalysis/` foundation, not to this optional downstream package.

Do not add a reverse import from native files. Keep one canonical native
statement and native evaluator when comparing alternative proofs. Bridge
existing definitions; do not replace them with Mathlib definitions. Do not
use a native endpoint identity to prove the integration bridge intended to
provide an independent Mathlib proof of that very identity.

Use the pinned compatible toolchain and Mathlib revision. Run both the source
boundary check and `ComparisonAudit.lean`. Mark an alternative proof as ready
only when all bridges are proved and its complete type matches the native
statement. Never equate absence of `sorryAx` with absence of all inherited
native-computation or standard Lean axioms. Report bridge and library costs
rather than only the final theorem's source length.
