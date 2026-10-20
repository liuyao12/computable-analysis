# Concrete geometric inverse-circle check

This snapshot contains the exact 52-module source closure of
`ComputableAnalysis.ArctanInverseCircleAudit`, including the concrete inverse
and circle computations being checked. It is a standalone proof bundle.

Install the Lean version in `lean-toolchain`, then run from this directory:

```sh
python3 scripts/run_arctan_inverse_circle_audit.py --source-root . --build-dir /tmp/arctan-circle-check --lean lean --jobs 2
```

No Lake packages or Mathlib are needed. The runner rebuilds every imported
project module with an isolated search path, then checks the theorem endpoints
and their axioms. It also writes a fresh `report.json` and `check.log` in the
chosen build directory. `verification/` contains the successful audit run;
its SHA-256 manifest binds the source files and checker to that result.

The check establishes inverse recovery and exact circle coordinates for every
rational slope in the unit chart, the unit-circle identity, first-quadrant
endpoints and geometric angle normalization. The quarter-chart comparison
retains its angle-equivalence premise. This bundle does not claim a new global
identification of every public trigonometric API. See the accompanying audit
for the remaining adapters, independent analytic comparison and domain work.
