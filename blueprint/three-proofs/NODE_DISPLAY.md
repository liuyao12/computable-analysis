# Statement boxes and Mathlib real backgrounds

The comparison build runs `ExportBlueprintStatements.lean` against exactly
the Lean declaration names in the chapter. Clicking a node shows its
mathematical statement, checked elaborated Lean type, and pinned source.
Short foundational definitions show their actual bodies; theorem proofs
are omitted. The common sink offers its definition and all three proof types.

`enhance_blueprint_nodes.py` computes a reverse dependency closure from the
root `Real` declaration in `Mathlib.Data.Real.Basic`. Lavender backgrounds
indicate actual transitive type/body dependence on that type, not merely a
Mathlib import or a namespace guess. Native nodes retain a pale green fill.
The common statement has no such dependence. Its combined-view background
is split because only one proof uses Mathlib reals; selecting a native proof
removes the shading, and selecting Mathlib shades it fully. Each positive
classification has an inspectable checked reference path to `Real`.

Browser tests check every visible node's mathematical and Lean statements,
source links, keyboard opening and closing, proof selection, route-sensitive
backgrounds, and mobile layout. This changes presentation and audit tooling,
not mathematical definitions or proofs.
