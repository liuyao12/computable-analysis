# Reciprocal-quartic π computation

`ComputableAnalysis/ReciprocalQuarticPi.lean` exposes the compact dyadic
quadrature

\[
  \int_{-1}^{1}\frac{1+x^2}{x^4-x^2+1}\,dx\ \Equiv\ \pi_{\rm area}.
\]

The formula is a useful test beyond the reciprocal-square kernel: it uses a
different rational density, an explicit (64/2^n) rectangle-box rate, and a
finite projective transport to the full-line Cauchy computation.

The module imports `CauchyPi`, not `PiProofs`:

1. `raw` is the literal reciprocal-quartic dyadic integral.
2. `raw_valid` certifies its shrinking rational intervals.
3. `raw_equiv_cauchyRaw` uses the explicit finite common envelope from
   `IntegralIdentities`, rather than transitivity of arbitrary box overlap.
4. `raw_equiv_piCircleArea` reaches the circle-area representative through
   the standalone Cauchy bridge.

Useful declarations:

- `ReciprocalQuarticPi.raw`, `ReciprocalQuarticPi.raw_valid`
- `ReciprocalQuarticPi.raw_width`
- `ReciprocalQuarticPi.raw_equiv_cauchyRaw`
- `ReciprocalQuarticPi.raw_equiv_piCircleArea`
