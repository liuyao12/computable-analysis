# One statement, three routes

The source chapter is `blueprint/src/06-three-cosine-proofs.tex`. It uses the
usual leanblueprint mathematical environments, `lean`, `leanok`, and `uses`.
Its final theorem occurs exactly once. A single proof environment holds the
three alternatives because the stock plastexdepgraph `proved_by` metadata
stores only one proof attachment; three separate attachments would overwrite
one another. The manuscript graph records the union of alternative proof
prerequisites, explicitly documented as such.

The focused graph is a view of the actual rendered manuscript graph. It
preserves the theorem modals and uses the usual definition-box / theorem-ellipse
convention. A route selector makes the alternatives explicit. Its 16 selected
landmarks contract actual stored Lean references; reduction happens separately
for each route, never across their union. The final proof declarations are
mapped to one statement sink. Type references back from a statement to a proof
are not added, avoiding artificial cycles. Every displayed edge has an exported
witness path, and all graphs are checked acyclic with exactly one target sink.

Run from the repository root:

```sh
lake build ComputableAnalysis.CosinePrimitive ComputableAnalysis.RotationSeries
(cd comparison && lake build && mkdir -p reports && lake env lean checks/ThreeProofsAudit.lean)
leanblueprint web
python3 blueprint/checks/build_three_proof_graph.py
```

The audit compares complete theorem types, rejects cross-route dependence,
checks that the native proofs contain no Mathlib dependencies, and verifies
that the third proof uses both the value bridges and independent quadrature.
It rejects transitive `sorryAx`. Existing upstream native-computation axioms
remain in the report. The snapshot includes source fingerprints and a pinned
revision. Expression counts concern only the final stored body, not the cost
of every prerequisite. Closure counts include helpers and are reported by
native, comparison, Mathlib, and Lean/other origin.

The native `RotationSeries.rotationExpRaw_valid` is an optional companion node.
It certifies a complex-box factorial-series computation at rational imaginary
inputs. It is neither Mathlib's exponential nor a fourth integral proof.
No full arbitrary-computable-input complex exponential is claimed here.

The optional Mathlib proof and independent validity proof are in
`comparison/MathlibComparison/CosinePrimitive.lean`. Their common statement is
`ComputableAnalysis.CosinePrimitive.Statement`; the native programs themselves
remain independent of the proof route. The third route does not call either
native endpoint proof or the native concave FTC.
