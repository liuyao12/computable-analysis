# Rectangular Cauchy integrals and analytic continuation

## What should the logarithm of \(-1\) mean?

The real logarithm starts at \(1\) and can move to any positive number by
integrating \(1/t\). To get to \(-1\) in the complex plane, we could go
above zero or below it. Should those trips give the same answer? In his
memoir on the dispute between Leibniz and Bernoulli, Euler took up the
same puzzle from the other end. If a logarithm of \(-1\) is a number \(z\)
for which the exponential gives \(-1\), how should we compute that
exponential at a complex input? [Euler's memoir](https://scholarlycommons.pacific.edu/euler-works/168/)

On the real line we already have three routes to the exponential. They
suggest three different things to try with complex numbers.

- Keep the power series and let \(z\) be complex:
  \(\sum_{k=0}^{\infty}z^k/k!\).
- Keep taking finer compound-interest steps and let \(z\) be complex:
  \(\lim_{n\to\infty}(1+z/n)^n\).
- Carry the reciprocal integral along paths near \(1\), then try to invert
  the resulting logarithm near its value \(0\), just as on the real line.

The second route lets us start with a finite calculation. Put
\[
 z_n=n\left(\cos\frac{\pi}{n}+i\sin\frac{\pi}{n}-1\right).
\]
The number \(1+z_n/n\) lies at angle \(\pi/n\) on the unit circle. Raising
it to the \(n\)-th power gives \(-1\), while \(z_n\) approaches \(i\pi\).
The same calculation with other odd multiples of \(\pi/n\) points to
other possible logarithms of \(-1\). This is part of Euler's argument.
For our box computations it raises a specific question: can we bound the
power approximation even while its input \(z_n\) is moving?

And why should the series, the power limit, and the inverse of the path
integral agree wherever their constructions overlap? Real agreement by
itself leaves plenty of freedom. For example, \(e^x\) and \(e^x+iy\)
give the same real values when \(z=x+iy\) lies on the real axis. We need
to find what distinguishes the proposed extensions. This is the question
that will lead us to the complex derivative.

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

Both constructions must actually be holomorphic on the region where we
compare them. Around zero, continuing the logarithm from \(1\) to \(-1\)
above and below gives \(\pi i\) and \(-\pi i\), respectively. The two
branches agree on the positive-side component of their overlap. The
negative-side component is disconnected from it. This is where the route
starts to matter, and where the next question about continuation begins.

`ComputableAnalysis.FunctionTheory.Holomorphic.identityOnConnected`
assumes valid represented inputs, holomorphicity of both maps, a shared
connected domain, and agreement on one neighborhood. It concludes that
the evaluations are equivalent at every valid represented point of that
domain. The real interval argument above explains how Taylor coefficients
give such a neighborhood in the mathematical example.
