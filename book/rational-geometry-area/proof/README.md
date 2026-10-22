# Finite rational area foundation checks

Install the Lean version in `lean-toolchain`, then run from this directory:

```sh
python3 scripts/run_rational_area_foundation.py --source-root . --build-dir /tmp/rational-area-check --lean lean
```

The module imports only `Init.Grind.Ordered.Rat`. The runner cold-builds it
with an isolated search path, checks the examples, and audits eleven theorem
endpoints. The successful source hashes, theorem list and checker output are
in `verification/`.

The abstract Pythagoras theorem assumes alternating bilinear parallelogram
content; it derives the square-area identity without a coordinate formula for
that content. Concrete finite checks include square contents, similarity
scaling, rational circle-chart and tangent equations, both polygon wedge-area
formulas, disk support, cubic gap and summed uniform fan estimates.

These results do not formalize a complete synthetic geometry, the derivation
of parallelogram bilinearity from polygon-area axioms, all polygon partition
and containment certificates, or the geometric area role of a complete sector
evaluator. The accompanying foundation proposal distinguishes those remaining
bridges from the checked finite statements.
