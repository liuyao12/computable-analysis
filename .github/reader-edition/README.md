# Computable Analysis reader edition

The canonical pi flashcards are in Chapter 1, immediately under **1.2.2 Other
examples**, after the square-root example. The ten cards include **Newton** and
**Complex logarithm**. Cosine quadrature remains in the worked comparison, not
in this gallery or a home-page teaser. The old catalogue URL redirects to the
chapter. The title remains **Computable _Analysis_**, with subtitle **An
alternative foundation to Calculus**.

`pi_flashcards.py` spells out early terms rather than hiding the numerical
pattern in summation/product notation. The Newton card evaluates the integrated
binomial series at 1/2, in modern unit-circle normalization. The historical
links lead to Newton's own account and notebook; no priority claim about the
first pi series is made. The logarithm card reads `i*pi/2 = Log(i)` and expands
to a calculation along the four rational steps of the straight segment 1 to i.
Both the real and imaginary enclosures are computed by exact rational arithmetic;
the error is at most `4 / ((N+1)*2^N)`. No numerical pi or logarithm library
value is supplied to that computation. The table is an illustration, NOT
extracted Lean output or a newly checked Lean continuation theorem.

The Gaussian expansion is only integrated on a fixed finite interval. It is
not incorrectly integrated term by term over the whole real line; improper
tails remain a separate obligation. The chapter-wide preview notice continues
to distinguish these mathematical identities from completed equivalence proofs.

This reader overlay is separate from the pinned verified mathematics snapshot.
The baseline reader pass/tests run before the placement/flashcard pass/tests.
The source revision, declarations, dependency witnesses, proof-map SVGs,
comparison metrics and reference pages are unchanged. Original Chapter 1 text
is preserved outside the added gallery and the renamed Other examples heading.
The existing equal-axis-scale cosine GIF, numerical data and worked comparison
are protected by hashes. The separate proof source revision is not overwritten
by the documentation revision.

Reproduce over the verified proof artifact:

```sh
python .github/reader-edition/analysis_edition.py --site site --revision REVISION
python .github/reader-edition/test_edition.py --site site --report reader-edition-tests
python .github/reader-edition/place_catalogue.py --site site --revision REVISION
python .github/reader-edition/test_placement.py --site site --report reader-edition-tests
```

Publication requires the full earlier proof verification, exact finite-term and
continuation-path checks, outward-rounded enclosure checks, all expanded-card
MathJax rendering, mobile layouts, legacy navigation, and unchanged artifacts.
The deployed HTML and calculation JSON are fetched and checked after Pages
reports success. No new native or Mathlib equivalence is claimed by this update.
