# Rectangular Cauchy integrals and analytic continuation

## Three routes to the exponential

We already have three ways to compute the same real exponential. Each
suggests a different way to make sense of \(\exp z\) for complex \(z\).

- **Invert an integral.** On the real line we solve
  \(\int_1^w dt/t=z\) for \(w>0\). For complex \(w\) near \(1\), integrate
  \(1/\zeta\) along a path from \(1\) to \(w\) inside a disk that avoids
  zero, then try to solve the same equation for \(z\) near \(0\).
- **Take smaller multiplicative steps.** Divide \(z\) into \(n\) equal
  increments and take the limit of \((1+z/n)^n\).
- **Sum the power series.** Evaluate \(\sum_{k=0}^\infty z^k/k!\) with a
  complex input.

Where all three recipes make sense, why should they agree off the real
axis? Agreement on the real line leaves plenty of freedom.
At \(z=x+iy\), the rules \(e^x\) and \(e^x+iy\) give the same real values
and differ whenever \(y\ne0\). What condition could tie the off-axis values
to the real ones? That is the question that leads us to the complex derivative.

## Two calculations for the same logarithm

Take the real logarithm, normalized by \(\log 1=0\). In the [integral
chapter](03-integrals.md), the section on monotone dyadic quadrature found
it by accumulating \(1/t\) from \(1\) to \(x\). There are two
different ways to ask what this function should do at \(1+i/2\).

One route is to substitute a complex input into the power series
\[
 L_{\mathrm{series}}(z)=\sum_{n=1}^{\infty}
 \frac{(-1)^{n-1}(z-1)^n}{n},\qquad |z-1|<1.
\]
The other is to integrate \(1/\zeta\) from \(1\) to \(z\), moving first
horizontally and then vertically in the right half-plane. At \(1+i/2\)
only the vertical leg contributes. Since \(i/(1+it)=(t+i)/(1+t^2)\),
the two coordinates come from familiar real integrals.
\[
 L_{\mathrm{path}}(1+i/2)
 =\int_0^{1/2}\frac{t+i}{1+t^2}\,dt
 =\frac12\log\frac54+i\arctan\frac12.
\]

Which answer should we call the logarithm? The miracle is that both
constructions are holomorphic where they are defined, and they already agree
on the real interval \(0<x<2\), where integrating the geometric series
gives the displayed logarithm series. That interval fixes their agreement on
the whole disk \(|z-1|<1\). We get the same answer at \(1+i/2\) by
summing complex powers or by accumulating along a path. The endpoint
derivative explains why the path construction is holomorphic: inside a
rectangle avoiding the pole, the derivative of the definite integral is
\(1/z\).

This is the principle of analytic continuation in action. A short real
interval fixes all the Taylor coefficients at an interior point of that
interval, since for a holomorphic function the derivatives in the real
direction are the complex derivatives there. The common series gives a
disk of agreement. At a new center inside that disk the same reasoning
starts again. Agreement spreads through the connected common domain.
This is what lets independently constructed extensions of a real function
meet in the complex plane.

## Where the coefficients come from

Let \(a\) be an interior point and choose a rectangle around it whose
boundary stays a positive distance from \(a\). The horizontal and vertical
sides let us compute with rational enclosures. Along the boundary,
expand the Cauchy kernel for \(z\) sufficiently close to \(a\).
Finite geometric division gives the coefficients and a remainder bounded
using that separation. Integrating the finite expansion keeps the
coefficient computations and tail estimates explicit. The local Taylor
evidence is derived from the holomorphic map and the rectangular contour.

## How far can the agreement travel?

For the exponential, the comparison applies on a connected common
region containing the real interval of agreement, once each recipe has
been shown to be holomorphic there. The inverse of the reciprocal
integral starts near \(z=0\), while the factorial series makes sense on
the whole plane. Agreement on the common region identifies the local
inverse with the function we can then continue by the series.

Routes matter when we continue the logarithm itself. Start with value
\(0\) at \(1\) and integrate the reciprocal once counterclockwise around
zero. The path returns to \(1\), while the integral has gained \(2\pi i\).
The two local logarithms at \(1\) now have different values. Comparing
routes is a separate question from comparing constructions that already
agree on a starting neighborhood of a common domain.

`ComputableAnalysis.FunctionTheory.Holomorphic.identityOnConnected`
assumes valid represented inputs, holomorphicity of both maps, a shared
connected domain, and agreement on one neighborhood. It concludes that
the evaluations are equivalent at every valid represented point of that
domain. The real interval argument above explains how Taylor coefficients
give such a neighborhood in the mathematical example.
