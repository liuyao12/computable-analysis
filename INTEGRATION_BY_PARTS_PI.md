# Finite integration-by-parts mesh π computation

`ComputableAnalysis/IntegrationByPartsPi.lean` is the direct π bridge for the
literal common-subdivision mesh behind the integration-by-parts animation.

At each finite stage the mesh carries a rational corner-error budget.  The
candidate boxes are prefix-stabilized to form a valid raw real; the resulting
computation agrees with the exact reciprocal-square rectangle raw, and hence
with the circle-area π computation.

This is distinct from `LogarithmicPi.lean`: it does not use the reciprocal
logarithmic endpoint or claim the general integration-by-parts theorem.  It
is a direct finite regression for paired rational subdivisions.

Useful declarations:

- `IntegrationByPartsPi.raw`, `IntegrationByPartsPi.raw_valid`
- `IntegrationByPartsPi.raw_equiv_rectangleRaw`
- `IntegrationByPartsPi.raw_equiv_piCircleArea`
