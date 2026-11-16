# Rectangular Cauchy integrals and analytic continuation

How much of a holomorphic function is determined by its values near one
point? Start with a small rectangle contained in its open domain. Its
boundary consists of horizontal and vertical segments, so each contour
integral can be computed along straight sides using axis-aligned rational
enclosures.

## Construct the local coefficients

Let \(a\) be an interior point and choose a rectangle around it whose
boundary stays a positive distance from \(a\). Along the boundary,
expand the Cauchy kernel for \(z\) sufficiently close to \(a\).
Finite geometric division gives the coefficients and a remainder bounded
using that separation. Integrating the finite expansion keeps the
coefficient computations and tail estimates explicit. The local Taylor
evidence is derived from the holomorphic map and the rectangular contour.

## Propagate agreement

If two holomorphic maps agree near a point, their local coefficients
agree there. At a point where all their Taylor coefficients agree, the
convergence bounds give agreement on another neighborhood. Agreement of
all coefficients also persists at limit points in the common domain by
continuity. Connectedness propagates this equality across the domain.

`ComputableAnalysis.FunctionTheory.Holomorphic.identityOnConnected`
assumes valid represented inputs, holomorphicity of both maps, a shared
connected domain, and agreement on one neighborhood. It concludes that
the evaluations are equivalent at every valid represented point of that
domain. To compare extensions on different domains, restrict to the
connected common region containing the starting neighborhood. This is the
uniqueness step used after constructing the extensions.
