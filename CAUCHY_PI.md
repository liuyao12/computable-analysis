# Cauchy full-line π computation

`ComputableAnalysis/CauchyPi.lean` is the small, standalone proof route for

\[
  \int_{-\infty}^{\infty}\frac{dx}{1+x^2}\ \Equiv\ \pi_{\rm area}.
\]

It imports `IntegralIdentities`, not `PiProofs`.  That distinction is
intentional: the theorem is usable without pulling the presentation registry
into another development.

The construction is finite at every stage.

1. `IntegralIdentities.cauchyFullLineIntegral` folds the two rational tails
   by evenness and `x ↦ 1/x` onto the compact unit interval.
2. `CauchyPi.raw_compute_eq_rectangleRaw` proves that this box is exactly the
   box of four reciprocal-square rectangle sums at the same stage.
3. `CauchyPi.rectangleRaw_equiv_piCircleArea` connects that compact rectangle
   algorithm to the geometric circle-area representative through
   `arctan.geom`.
4. `CauchyPi.raw_equiv_piCircleArea` transports the stagewise equality to the
   full-line construction.

There is no completed-real improper integral in this route.  `raw_valid` is
the certificate that its nested rational boxes shrink, and `Equiv` says that
two such algorithms overlap at every common stage.

Useful declarations:

- `CauchyPi.raw`, `CauchyPi.raw_valid`
- `CauchyPi.raw_compute_eq_rectangleRaw`
- `CauchyPi.raw_equiv_piCircleArea`
- `CauchyPi.symmetricRaw`, `CauchyPi.symmetricRaw_valid`
- `CauchyPi.symmetricRaw_equiv_rectangleRaw`
- `CauchyPi.symmetricRaw_equiv_piCircleArea`

`symmetricRaw` is the companion bounded calculation.  It splits at zero,
uses the increasing and decreasing branches separately, and proves that the
two-piece finite assembly meets the same rectangle raw.  It is therefore a
separate regression for the piecewise-monotone interface, not an alternate
name for the full-line evaluator.

The blueprint treatment is in the “Projective and improper test integrals”
section of `blueprint/src/03-integrals.tex`.
