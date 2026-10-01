# Pedagogical exposition

The reader should understand the question before meeting the apparatus used to
answer it. This is the project-wide preference for chapters, worked examples,
construction guides and future directions. It does not impose a fixed page
layout or require repeated introductions to material already motivated.

Start where a reader can reason: a concrete computation, an application, a
surprising proposed identity or an obstacle. Explain what remains unclear.
Introduce the next definition, estimate or hypothesis as a response to that
problem. A motivating strategy need not match the cleanest final proof; show
why the strategy was plausible and what the proof actually uses.

At major transitions, explain the role of the next step. For example, a series
needs a remainder because a finite prefix cannot control the missing terms;
whole-cell bounds support a rectangle integral because point samples can miss
a peak; a uniqueness argument turns reflection symmetry into exact line
location because symmetry alone permits two distinct reflected roots.

Use earlier material deliberately. Link to the specific chapter or section
that supplies the motivation, then say what new question is being asked here.
The construction guides should be usable after those chapters, with brief
context followed by the function-specific strategy. Their maintained Markdown
and downloadable editions must agree.

Keep mathematical statements exact. Do not weaken domains or suppress branch,
pole, convergence or existence conditions to simplify the story. Keep checked
native results, conditional laws, external comparisons and unfinished targets
visibly distinct. Code inventories belong after the explanation or in linked
proof viewers; they do not motivate a theorem by themselves.

## Maintained reader review

`book/pedagogy/pages.json` reviews every top-level narrative reader page.
It preserves existing effective openings and supplies problem-first additions
and section transitions where the current reader needs them. Markdown guide
openings live in their own skill sources. Redirects, generated graph surfaces
and the technical reference are supplementary destinations reached from the
motivated book pages; they are not additional chapter introductions.

The final narrative layer is applied after the existing verification editions.
`reading/pedagogy-edition.json` records the exact before and after hashes,
retained page rationale, links to earlier motivation, and the checks preserving
all pre-existing formulas, MathML, code, theorem blocks, script sources, links
and anchors. It also records all delivered narrative page hashes. Earlier
edition reports remain immutable snapshots of the stages they audited.
Live verification follows the explicit narrative hash transition when a page
has been superseded; it does not discard the earlier hash check.

Run the final-layer coverage, preservation and rendering checks with:

```sh
python3 .github/reader-edition/pedagogy.py --site site --revision COMMIT_SHA
python3 .github/reader-edition/test_pedagogy.py --site site --report pedagogy-checks
```

These mechanical checks protect coverage and existing mathematics. They do not
judge whether the exposition teaches well; that requires reading the actual
question, example and progression. Revise this review whenever the book grows.
