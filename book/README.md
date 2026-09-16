# A mathematics-first book with inspectable proofs

The reader is a book, not a dashboard or a rendered API catalogue. Chapters 1
and 2 remain in their original TeX files; `preserved-chapters.json` pins their
bytes. The other existing mathematical chapters are retained as manuscript
material, not silently promoted to fully checked developments. New reader
chapters live here. The old blueprint output remains a technical reference.

## Reading layers

1. Mathematical narrative: definitions, hypotheses, statements and proof ideas.
2. Beside each theorem: a **Proof map** link. It opens selected mathematical
   bundles, not the whole declaration graph, without losing the reading place.
3. Inside a bundle: the mathematical role and statements first, then optional
   exact, syntax-colored Lean declarations with provenance.
4. Comparisons, size accounting, source files, and trust audits are secondary.

`build.py` imports the existing TeX-rendered chapter bodies. It does not change
the authors' mathematics to suit a documentation template. Original chapter
HTML, resources and the old graph are retained under `reference/`. Old URLs
remain usable. Neither front-end page CSS nor the reader's graph interface
uses the old blueprint theme. The legacy renderer is currently only a TeX
conversion step and the source of historical cross-reference anchors.

The cosine example reuses the checked bundle/statement exports and actual
reference witnesses. Mathematical overview maps for other manuscript theorems
are explicitly labeled **editorial, comparison not registered**. They are not
asserted to be dependency-extracted proofs. There is no invented Mathlib proof
or empty green placeholder. New paired cases should be registered in
`comparison/proof-bench/cases.tsv` and gain extracted maps after verification.

## Build

Run after the existing proof exports, leanblueprint render, bundle audit, and
proof-bench build:

```sh
(cd comparison && lake env lean checks/ComputabilityAudit.lean)
python3 book/checks/source_boundary.py
python3 book/build.py
python3 book/checks/test_book.py
python3 book/checks/browser.py
```

The new builder replaces only published HTML entry points, not mathematical
sources. A changed mathematical source invalidates the pinned source snapshot
and requires fresh formal checks. The preserved chapter hash gate is deliberate:
editing those chapters needs an explicit review and baseline update.

## Native computability

The native and Mathlib packages stay one-way. `source_boundary.py` inventories
existing `noncomputable` declarations and refuses new ones outside its reviewed
baseline. This is a migration inventory, not an exemption that makes them
computable. The Lean audit traverses types and stored bodies for the published
native constructors and proofs, reports noncomputable tags by ownership, and
compiles/runs smoke evaluations. Source scanning alone is not a computability
proof. Classical reasoning in proofs, native-computation axioms, termination
proofs and executable data paths are different issues and are reported as such.

No claim is made that the full historical repository is already free of
noncomputable definitions, or that the current set of examples already covers
most science and engineering. That is the programme to develop and test.
