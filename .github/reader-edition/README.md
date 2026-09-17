# Computable Analysis reader edition

The canonical pi flashcards are in Chapter 1, immediately under **1.2.2 Other
examples**, after the square-root example. There are eleven cards, including
**Newton**, **Machin**, and **Complex logarithm**. Cosine quadrature remains in
the worked comparison, not in this gallery or a home-page teaser. The old
catalogue URL redirects to the chapter. The title remains **Computable
_Analysis_**, with subtitle **An alternative foundation to Calculus**.

## Visible coefficient patterns and alternative computations

The Newton card now keeps its coefficients factored: 1/2, (1*1)/(2*4),
(1*1*3)/(2*4*6), and so on. Each is followed by the integrated odd power
(1/2)^(2k+1)/(2k+1). Its details give the coefficient recurrence, general term,
and the positive-term ratio (2k-1)(2k+1)/(4(2k+2)(2k+3)) < 1/4. The original
modern normalization and primary-source historical link are retained.

Machin is pi/4 = 4 atan(1/5) - atan(1/239). Its card shows the first terms of
both alternating series, the explicit next-term error budget, and the rational
addition calculation with its angle-range condition.

The Log(i) card still reads i*pi/2 = Log(i). Its expanded panel now contains
three independent finite algorithms for the same principal branch:

1. Four local Taylor series on the straight segment from 1 to i.
2. Two symmetric series H(z)=2(z+z^3/3+...) using the midpoint (1+i)/2.
3. Machin's combination 4 H(i/5)-H(i/239).

`pi_patterns.py` calculates all displayed prefixes and bounds in exact rational
arithmetic. It checks the local input bounds, Gaussian-rational products, and
rational inequalities locating the branch. A product identity alone is not
treated as a valid logarithm identity. Both decimal endpoints and printed
scientific-notation error bounds round outwards. N is terms per series, not
an equal-runtime benchmark (the first method evaluates four series, the others
two). No numerical pi or logarithm constant is read by these algorithms.

## Scope and preservation

These are mathematical preview cards and independently computed illustrations,
not extracted Lean output or new formalized representation bridges. No new Lean
proof, equivalence badge, or proof-length score is claimed. The checked proof
snapshot, dependency witnesses, measurements, previous numerical records and
worked illustrations remain unchanged. Formula placement and all original
Chapter 1 text outside the added gallery are preserved.

The final pattern pass runs only after the earlier reader and flashcard tests.
All stages start from the pinned verified proof artifact, not a mutable copy
of a previously rendered site. Metadata distinguishes the new documentation
revision from the unchanged mathematical proof revision. Previous numerical
records remain available; the current patterns, methods and error bounds are
in `reading/pi-patterns.json`.

## Reproduction

```sh
python .github/reader-edition/analysis_edition.py --site site --revision REVISION
python .github/reader-edition/test_edition.py --site site --report reader-edition-tests
python .github/reader-edition/place_catalogue.py --site site --revision REVISION
python .github/reader-edition/test_placement.py --site site --report reader-edition-tests
python .github/reader-edition/pi_patterns.py --site site --revision REVISION
python .github/reader-edition/test_pi_patterns.py --site site --report reader-edition-tests
```

Publication requires the complete preceding proof verification and every reader
stage's tests. The final tests inspect exact coefficient patterns, tail bounds,
branch inputs, all three numerical logarithm methods, eleven-card placement,
rendered MathJax, mobile layout and preservation hashes. The live HTML, JSON
revision, worked illustration and proof-source manifest are checked again after
Pages reports success.
