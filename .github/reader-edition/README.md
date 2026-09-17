# Computable Analysis reader edition

The title is **Computable _Analysis_**, with subtitle **An alternative foundation
to Calculus**. The home page directly displays the cosine-quadrature teaser
`1/pi = integral_0^(1/2) cos(pi*x) dx`, with no C wrapper notation, and links
to the ten-entry pi catalogue restored in Chapter 1 and its own reader page.
The catalogue is a preview, not a claim that every native equivalence is proved.
It reconstructs the formulas; it does not claim to recover the old image file.

This publication overlay is deliberately separate from the checked theorem
source. The Pages workflow requires the completed integral-portfolio verification
and validates its exact source revision before applying the reader edition.
The new documentation revision is stored in `reading/analysis-edition.json`;
all original proof-source revisions, declaration text, dependency witnesses,
proof-map SVGs, measurement JSONs and reference pages are retained. The old
animation manifest remains the record of that previous snapshot; the current
cosine illustration and hashes are in `reading/cosine-half-interval.json` and
the edition record. No Lean proof is added or reclassified by this update.

The corrected cosine GIF keeps the upper endpoint at 1/2 throughout, with 300
pixels per unit on both axes. Dyadic endpoint rectangles are evaluated from
positive half-angle square-root intervals. Geometric pi is evaluated independently
from rational inner/outer sector polygons, then reciprocated. Only raster
positions use floating point. Displayed bounds use exact rational arithmetic and
outward rounding. These are illustrative Python computations, NOT executions of
the literal Lean output schedules. The GIF, poster, table, chapter caption and
proof-panel captions use the same endpoint and provenance.

Reproduction over the verified artifact:

```sh
python .github/reader-edition/analysis_edition.py --site site --revision REVISION
python .github/reader-edition/test_edition.py --site site --report reader-edition-tests
```

The full tests require a browser with MathJax CDN access. They test mathematical
rendering (including the continued fraction), the home-to-Chapter-1 link, all ten
formula cards, title italics, mobile layout, image pause/play and reduced motion,
fixed-axis-scale metadata, exact numerical bounds, an existing proof-map popup,
and preservation of the checked proof artifacts. Publication stops on failure
and checks live HTTP content and GIF hashes after deployment.
