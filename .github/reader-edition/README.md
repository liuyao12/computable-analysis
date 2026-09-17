# Computable Analysis reader edition

The title is **Computable _Analysis_**, with subtitle **An alternative foundation
to Calculus**. The pi catalogue's canonical location is now Chapter 1, immediately
under **1.2.2 Other examples**, following the square-root example. It contains
nine formulas. Cosine quadrature is reserved for the worked comparison, and is
not duplicated in the gallery or as a home-page teaser. The home navigation
points to the chapter. The former `pi-computations.html` bookmark redirects there.

The catalogue reconstructs the mathematical formulas, not the original image.
It is a preview, not a claim that every native equivalence has been proved.
The original chapter mathematics is retained; only the Other examples heading
and the placement/content of the added gallery change.

This reader overlay is separate from the checked theorem source. Pages requires
the completed integral-portfolio verification and checks its exact source SHA.
The baseline edition pass and its tests still run first; the final placement
pass and tests then apply the requested chapter organization. Publication never
skips the proof-data preservation, numerical bounds or browser gates.

The cosine GIF stays in the worked comparison: fixed endpoint 1/2, equal x/y
scales, rational nested-radical sample bounds, and independently computed geometric
reciprocal bounds. It and the worked chapter's mathematical content remain
unchanged by the placement pass. The illustration is not literal Lean output.

Reproduce over the verified proof artifact:

```sh
python .github/reader-edition/analysis_edition.py --site site --revision REVISION
python .github/reader-edition/test_edition.py --site site --report reader-edition-tests
python .github/reader-edition/place_catalogue.py --site site --revision REVISION
python .github/reader-edition/test_placement.py --site site --report reader-edition-tests
```

`reading/analysis-edition.json` describes the final edition;
`reading/catalogue-placement.json` records placement and preservation checks.
Original proof revisions, exact declaration text, dependency witnesses, graph
SVGs and measurement JSONs remain unchanged. The original animation manifest
remains historical; current cosine metadata is in `cosine-half-interval.json`.
No new Lean result is claimed by these documentation updates.

The final tests check DOM order under Other examples, absence of the cosine
card/teaser, all nine mathematical formula renderings, desktop/mobile layout,
home navigation, old-page redirect, and preservation of the worked comparison,
proof data and exact GIF bytes. Live HTTP checks repeat the essential assertions
and verify the deployment revision and animation hash after publication.
