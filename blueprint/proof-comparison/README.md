# Measured proof comparison

This is the frontend for two named proofs of the same cosine-integral
proposition. No production theorem is changed by this measurement tool.

Build the relevant proofs, then run:

```sh
python3 blueprint/checks/check_two_cosine_proofs.py
lake env lean blueprint/checks/ExportProofComparison.lean
leanblueprint web
python3 blueprint/checks/build_proof_comparison.py
python3 blueprint/checks/test_proof_comparison.py --manuscript
```

The exporter follows actual constants in stored bodies and types, not module
imports. The overview contracts paths between selected declarations; every
edge carries a reference-path witness. The full raw graph is downloadable
and searchable. Companion derivative results are shown separately and are
not added to either final proof's dependency count.

Expression-tree counts retain multiplicity. Distinct-subexpression counts
use structural Expr equality within each declaration. Closure totals count
each declaration once; neither representation unfolds named constants.
Source counts union compiler-reported ranges before removing comments and
blank lines. Counts are descriptive, not a proof-quality score.

Kernel timing is a synchronous Kernel.check of each final stored proof plus
Kernel.isDefEq against its declared type, with the prerequisite environment
already loaded. Eleven samples follow a discarded warmup. Imports, tactic
elaboration, and recursively rechecking prerequisites are excluded. Per-trial
inert metadata prevents loop-invariant hoisting. Timings are environmental,
not end-to-end build benchmarks.

The site build runs the existing independence/axiom audit before generating
data, pins its exact Git source SHA, and publishes source-file fingerprints.
Axiom counts use Lean's collectAxioms, not just the syntactic edge traversal:
the kernel's trust collection can include implicit dependencies not exposed
as a direct Expr constant reference.

The manuscript chapter and native graph include both proof paths and link to
this measured explorer. The richer graph must not imply that a companion
computed-derivative validity theorem is itself referenced by a final proof.
