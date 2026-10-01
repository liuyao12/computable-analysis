# Bundled theorem comparisons

The reader's common comparison viewer covers all 22 registered theorem maps,
the existing four-route Leibniz comparison, and 13 newer showcase statements.
Each theorem has route selections and a Mathlib comparison slot. Slots without
a registered proof are labelled pending. Related analytic ingredients are not
presented as a proof of a stronger showcase theorem.

The original audited maps, exact declaration paths, theorem statements and
scope ledgers remain available. The common viewer preserves those bundles
and arrows, and adds curated mathematical routes for newer pages. Curated
arrows describe prerequisites in an argument; they do not assert an extracted
Lean dependency or logical indispensability. In particular, the zeta first-
and second-zero routes remain plans, with only the conditional reflection
lemma currently checked.

## Source LOC

A node counts the union of its recorded Lean declaration spans. If a reference
has no known end line, the entire named file is counted and the badge says
“file LOC”. Counts remove nested block comments and line comments, preserving
comment-like text in strings and character literals, and ignore blank lines.
A file-level count includes declarations outside the intended bundle.

A route total takes the union of source lines across its nodes, avoiding double
counting shared files and overlapping spans. Sources assigned to a bundle are
not automatically expanded through imports. These are source inventories,
not minimal proof sizes, elaborated-term sizes, runtime measurements, or
substitutes for theorem and axiom audits. Unknown and pending sizes are not
zero. A displayed total with pending bundles is only the measured portion.

The pinned inventory records source URLs, SHA-256 hashes, physical line counts,
and a bitmap identifying counted code lines. Publication checks fetch those
exact revisions and reproduce the inventory. Current local Lean files are
measured from the publication revision. The JSON download includes every
node's spans and every route's union inventory.

## Reproduction

After preparing the reader using the normal publication workflow:

```sh
python3 .github/reader-edition/test_proof_bundles.py \
  --site site --report reader-edition-tests/proof-bundles --verify-sources
```

The test checks registered-map coverage, acyclic arrows, proof-route filtering,
source bounds, shared-line de-duplication, keyboard selection, responsive
layout, and pending-zero scope. It does not claim new mathematical proofs.
Add future showcase routes to `book/proof-bundles/catalogue.json`, using source
links and the exact proved scope; leave unfinished nodes pending.
