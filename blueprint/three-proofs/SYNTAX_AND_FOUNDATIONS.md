# Syntax highlighting and shared rational foundations

The common graph root is Lean's `Rat` (Q). It feeds native interval
computations and Mathlib's real numbers. The Mathlib-real construction node
is distinct from the `Represents` interpretation node in the third proof.
The `Real.ofCauchy` constructor is an anchor so the construction's reference
to rational Cauchy sequences is represented by an actual witness path; the
type constant `Real` alone has no body containing that constructor signature.

The broad nodes still display curated groups of checked Lean declarations.
`lean-highlight.js` wraps the exact exported text in colored spans. Nested
comments, strings, escaped identifiers and Unicode identifiers are handled.
This is lexical syntax coloring, not claimed semantic token information.
Text content and Copy remain identical to the export. All token content is
inserted using text nodes, not interpreted as HTML.

`proof_lanes.py` groups shared native constructions and Mathlib foundations
separately from the direct, native-FTC and Mathlib/bridge proof lanes. The
latter converge at the same statement. Rank and cluster constraints are
layout only; no visible dependency is invented and no actual proof is
changed. Shared prerequisites remain visible, rather than being falsely
claimed independent. Reduction stays separate for each route.

Node/card green and lavender backgrounds retain their original meaning:
transitive dependence on Mathlib's `Real`, independently of syntax colors.
The rational node is Mathlib-real-free, the Mathlib-real construction node is
shaded, and the common statement's three alternative proof roots retain
separate classifications. Core Lean source links point to lean4, not Mathlib.

CI reruns the proof/type/dependency audits, exports all grouped declarations,
checks lexer text preservation, and browser-tests the new rational root,
separate route clusters, every snippet, Copy, route filters and mobile layout.
