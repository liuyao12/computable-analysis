# Complete the elementary calculus core

The present milestone is ordinary, finite-valued single-variable calculus.
Extended endpoints, singular-function observations, hyperfunctions, spectral
theory, and general PDE frameworks are not prerequisites and are not being
introduced into the elementary entry points. Gamma and Stirling remain
independent projects. No previous experimental file needs to be deleted.

## First completed step: Taylor from the existing FTC

`ComputableAnalysis.TaylorFTC` now constructs the derivative model for

    G_n(t) = sum_{k=0}^n (b-t)^k F_k(t)/k!,   F_k' = F_{k+1}.

The product rule cancels every term except

    G_n'(t) = (b-t)^n F_{n+1}(t)/n!.

Applying the existing finite-sample FTC gives the integral remainder.
Applying it again to a polynomial majorant gives

    |F_0(b) - sum_{k=0}^n (b-a)^k F_k(a)/k!|
        <= M (b-a)^(n+1)/(n+1)!.

The statements quantify over arbitrary finite order. They require the
existing local quadratic-remainder `Model` at each link of the derivative
chain, and a bound on the last derivative. This is a sufficient quantitative
regularity hypothesis, not an assertion about all pointwise differentiable
functions. The current interface uses a certified unit chart and arbitrary
rational subintervals 0 <= a < b <= 1. Applications on other intervals must
supply the corresponding reparametrized derivative certificates; a general
new affine-chart transport theorem is not claimed by this patch.

`integral_remainder` describes an independently supplied quadrature through
its finite mesh-error estimate, not by assuming the endpoint value. Its
`integral_remainder_equiv` theorem compares actual native `RealRaw` programs.
`remainder_bound` proves the factorial bound with vanishing evaluation slack;
`approximation_intervals` removes the slack and constrains every pair of
stages of the polynomial and value computations. The earlier finite
coefficient-error theorem remains available for inexact Taylor coefficients.
None of these statements asserts convergence of an infinite Taylor series.

## Nonpolynomial regression

`TaylorReciprocal` supplies every derivative model for f(x)=1/(2-x), rather
than taking a Taylor expansion as a hypothesis. Its remainder is independently
computed by the existing rational-Lipschitz dyadic quadrature:

    I_n = (n+1) integral_0^1 (1-x)^n/(2-x)^(n+2) dx.

Validity uses the finite Lipschitz constant 2n+2 for the normalized integrand,
not Taylor. Applying the new general Taylor theorem then proves

    I_n = 2^(-n-1),
    sum_{k=0}^n f^(k)(0)/k! = 1 - 2^(-n-1).

`CheckTaylorFTC.lean` verifies this dependency distinction, exports exact
statements and inherited axioms, and evaluates actual quadrature stages.
The mesh bounds are conservative; this is not a fast integral algorithm.

Power differentiation was extracted from the Cartwright-dependent
`UnitPowerCalculus` into `FiniteSamplePowers`, without renaming its public
operations. The earlier applications can still import the old entry point.

## Next elementary completion targets

Keep the narrative on mathematics and applications, with implementation
certificates and exact statements in the theorem-side panels.

1. **Differentiation and local approximation.** Consolidate sum, product,
   quotient, chain and inverse rules on supplied rational intervals. Expose
   tangent and sensitivity estimates, and transport the Taylor theorem across
   affine charts. Reuse the existing computed-input composition machinery.
2. **Definite integration.** Finish the concrete user interfaces for additivity,
   reversal of endpoints, integration by parts and substitution. State the
   endpoint FTC for the actual quadrature programs and instantiate ordinary
   exponential, trigonometric, reciprocal and logarithmic examples.
3. **Optimization and equations.** Use derivative signs, convexity and finite
   enclosures to certify extrema and roots on specified intervals. Prefer
   constructive brackets and error bounds to unspecified chosen points.
4. **Elementary approximation.** Connect finite Taylor approximations to the
   existing exp/log/trigonometric algorithms, and then cover geometric,
   alternating and factorial tails. Convergent Taylor series and asymptotic
   expansions remain distinct notions.

These are completion targets, not claims that each interface is already
finished. No new comparison proof or proof-size measurement is claimed for
the Taylor package. An independent Mathlib proof of the same native assertions
and integration into the published theorem maps remain separate delivery
steps; the old comparison data have not been regenerated or modified here.
