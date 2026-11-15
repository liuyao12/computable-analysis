# Computable Analysis: a living foundation

This is the editable mathematical text for the reusable foundation. Its source
is this directory of Markdown files. Definitions, proposition statements,
proofs, and explanations can evolve together through ordinary Git changes.
Publication on Prove2Me is a later, selective export of stable declarations;
it does not freeze this book or the development repository.

The subject is analysis built from rational interval and box computations.
The opening sequence follows numbers and functions, Archimedean circle and
sphere computations, then function-specific integration and the fundamental
theorem of calculus, introducing derivatives through constructed secant limits. It states precise
propositions and construction obligations without an exercise-driven teaching
layer. A few compact reference constructions help contributing agents;
the larger worked-example catalogue stays in the companion subproject.

## Contents

- [Purpose, scope, and mathematical contract](00-charter.md)
- [Chapter 1. Computable numbers and functions](01-numbers-and-functions.md)
- [Chapter 2. Circle, sphere, and arctangent](02-circle-sphere-and-arctangent.md)
- [Chapter 3. Integration, derivatives, and the fundamental theorem](03-integrals.md)
- [Worked example. The Gaussian integral](03a-gaussian-integral.md)
- [Chapter 4. Infinite series with certified errors](04-infinite-series.md)
- [Chapter 5. Power series and uniform tail bounds](05-power-series.md)
- [Chapter 6. Taylor expansions from FTC](06-taylor.md)
- [Chapter 7. An improper integral from two computations](06a-dirichlet-integral.md)
- [Chapter 8. Continued fractions and pi](06b-continued-fractions.md)
- [Compact reference constructions for agents](07-agent-reference.md)
- [Proposition ledger and contribution roadmap](08-roadmap.md)
- [How to contribute and revise the foundation](09-contributing.md)

Preliminary material for later chapters is retained under `textbook/notes/`.
It is outside this opening sequence. Euler's identity, broader complex
analysis, and ODEs can be developed after the geometric calculus and Taylor
comparison. The latter follows the general series and power-series chapters.

## Reading the status labels

**Existing definition** names a definition already in the selected source.
**Existing theorem** names a proved source declaration, with its actual
hypotheses; the declaration check verifies that the name is available.
**Conditional law** is a complete theorem about supplied objects satisfying
its stated evidence. **Open target** is work proposed here, not an assertion
that a Lean theorem already exists. **Promotion work** concerns reusable
code currently in the companion because its imports are not yet independent.

An import inventory is not a semantic audit. The book does not claim that
every declaration in a selected module has been independently reviewed, or
that the foundation is complete. The [roadmap](08-roadmap.md) records the
distinction between the mathematical goal and the current build boundary.

## Sources and reproducibility

The authoritative module assignment is `foundation/modules.json`. Run
`python3 scripts/foundation_layout.py` to check the boundary and `lake build`
to check the foundation. `scripts/check_foundation_statements.lean` checks
the named entry declarations. The separate topic package is described in
`subprojects/special-topics/README.md`.

The online edition is generated from these same Markdown files. Edit the
Markdown, not generated HTML. Every mathematical expression uses LaTeX;
the online edition typesets it with KaTeX.

Running `python3 scripts/render_foundation_textbook.py` also prepares
`book/foundation-textbook/downloads/foundation-mission.md`: a combined,
editable manuscript with internal chapter links and the full
[Taylor from FTC skill](../skills/taylor-from-ftc/SKILL.md) as an appendix.
The web reader offers this manuscript and the standalone skill as downloads.
Agents receiving the manuscript can read the procedure without access to
repository skill files. Preparing this export does not submit a mission or
publish formal declarations.

## A guide other agents can use

Read the charter, the relevant chapter, the proposition ledger, and the
compact references before formalizing a new function. The text specifies
the mathematical role to prove; a construction skill suggests a method;
the actual Lean proof supplies the missing evidence. There is no single
recipe required for every derivative, inverse, or integral.
