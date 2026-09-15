# Grouped Lean statements in broad blueprint nodes

Each displayed node is a mathematical topic, not a single declaration.
`node-groups.tsv` explicitly curates its definitions, certificates, supporting
lemmas and conclusions. Every node has several statements. The exporter checks
all names in Lean and exports the exact elaborated types; selected definition
bodies are included, but theorem proof bodies are not.

The modal shows all declaration cards together in named groups, with group
navigation, a copy button and a pinned source link for every card. There is no
one-at-a-time declaration selector. Mathematical prose stays collapsed below
the Lean cards. Short prose node titles and the focused graph are unchanged.

The single conclusion node includes the proposition, all three proof signatures,
and the three validity results. Selecting a route highlights its proof card
without hiding the alternatives. Each card has its own transitive Mathlib Real
classification. In particular, the proposition and native proofs remain unshaded
while the Mathlib proof card is shaded, even in the shared-node modal.

Display-only companion declarations are labelled explicitly. The audit exports
and checks them, but does not add them to any proof's measured dependency closure.
The diagram's anchors, contracted proof paths, and route counts are unchanged.
`test_statement_boxes.py` compares every displayed card with the checked export,
tests the group links, exact copying, real-dependency badges, route highlighting,
keyboard interactions, and the mobile layout.
