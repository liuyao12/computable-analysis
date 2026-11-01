# How to contribute and revise the foundation

## Work in the editable source

Contribute code and this textbook through the repository's ordinary
collaboration workflow. The Markdown chapters can be revised as definitions,
proposition statements, and formal proofs develop. Corrections to a definition
should update affected statements, proofs, exposition, and status labels in
the same change.

Specialized topics and worked examples belong to the companion subproject.
Reusable general lemmas can move in the other direction after their
dependencies have been separated. Preserve module names where practical;
record unavoidable API changes explicitly.

## A mathematical contribution

State the full mathematical domain and intended conclusion first. Identify
the actual input and output constructions, required validity and analytic
evidence, sign or branch choices, and the relation expressing equality.
Prove quantitative supporting estimates and the public exact law. Keep
construction validity, mathematical identification, and comparison distinct.

Use the repository's formalization and function-construction skills when
applicable. Do not add a universal existence axiom, a placeholder proof, or a
record that assumes the result being advertised. An open mathematical target
can remain an explicitly labeled statement in this book until its interfaces
and hypotheses are ready to formalize.

For Taylor convergence derived from the actual function through repeated
FTC, use the [Taylor from FTC skill](../skills/taylor-from-ftc/SKILL.md).
Maintain its canonical repository file alongside the derivation in Chapter 6.
Regenerating the textbook copies the skill into the web downloads and embeds
its full instructions in the combined mission manuscript; do not edit those
generated copies separately.

## Verify the package boundary

From the repository root:

```sh
python3 scripts/foundation_layout.py
lake build
lake env lean scripts/check_foundation_statements.lean
python3 scripts/render_foundation_textbook.py --check
```

The first command checks source ownership and imports, not mathematical
correctness. The Lean commands check the selected source and the named
declarations. The final command checks that the online edition matches the
editable Markdown sources.

To work on a topic, use its downstream package:

```sh
cd subprojects/special-topics
lake update
lake build ComputableAnalysis.FiniteAMGMExample
```

That example command demonstrates the opt-in build boundary; it is not a
dependency of the foundation. A complete topic build may require locally
available source files and further work on that topic's existing proof state.

## Prove2Me publication

The repository and textbook stay the primary editable development sources.
Prove2Me hosts selected stable declarations and proof missions. Published
formal definitions and theorem statements are immutable there: a substantive
correction needs a replacement declaration and updated links. Existing
imports remain attached to their original declarations.

Publish incrementally. Do not freeze uncertain foundational interfaces merely
to invite collaboration, and do not imply that open targets are proved.
Platform mission proposals also require the account owner's statement review
and submission through the website. Preparing a precise draft is work an
agent can do; the final human review remains a separate step.
