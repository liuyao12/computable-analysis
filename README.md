# Computable calculus

An alternative foundation for calculus serving science and engineering through
terminating rational computations and proofs of their accuracy.

[Read the mathematical book](https://liuyao12.github.io/computable-analysis/)
· [The cosine primitive](https://liuyao12.github.io/computable-analysis/cosine.html)
· [Project purpose and migration](PROJECT.md)

## Mathematics first

The public book presents definitions, hypotheses, results and proof ideas.
The original Chapters 1 and 2 are preserved. Each theorem has a margin link to
its proof map: mathematical bundles rather than one node per declaration.
Exact syntax-colored Lean statements, provenance, and quantitative comparisons
are available behind that map, not mixed into the reading narrative.

The first fully paired comparison has three proofs of one computational cosine
primitive statement: direct inequalities, native FTC, and Mathlib with value
and quadrature bridges. Other manuscript theorem maps are labeled editorial
until their paired declarations and dependency paths are registered.

## Computational boundary

The native algorithms must not obtain numerical data from noncomputable
declarations or import Mathlib reals. The optional `comparison/` package imports
both foundations in the opposite direction. It identifies the same algorithms
with Mathlib's objects and proves the same propositions, not look-alike formulas.

The historical native source still contains 16 noncomputable helpers. They are
inventoried as migration debt, not silently promoted to the computational API.
The new audit checks selected native declaration closures, reports proof-only
external tags and axioms, and runs compiled numerical smoke tests. It is not a
claim that every historical file already meets the stricter goal.

## Work with the sources

```sh
# Native first example
lake build ComputableAnalysis.CosinePrimitive

# Optional comparison
cd comparison
lake update
lake build MathlibComparison
lake env lean checks/ThreeProofsAudit.lean
lake env lean checks/ComputabilityAudit.lean
```

The general native entry point remains `import ComputableAnalysis`; narrower
interfaces are documented in [GOALS.md](GOALS.md) and
[FORMALIZATION_GUIDE.md](FORMALIZATION_GUIDE.md). They are contributor references,
not the table of contents of the mathematical book.

See [book/README.md](book/README.md) for the reader build, preserved chapter gate,
theorem-map provenance, and boundary tests. The old detailed presentation and
bookmarks remain accessible. No theorem proof is changed by the reader redesign.

## Evidence, not a simplicity claim

The comparison suite records identical statements, independent proof routes,
validity, representation bridges and cumulative dependency costs. It currently
contains one calculus example plus a calibration, with further families planned.
Smaller proof terms for one representation do not establish a universally simpler
foundation or sufficient coverage of engineering practice. That broader claim
requires varied worked problems, explicit tolerances and verified computations.
