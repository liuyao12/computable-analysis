# Practical foundation programme

The next unit of work is a usable mathematical chapter, not a more general
exceptional-set theorem. Keep a concrete computation, its accuracy estimate,
a reusable calculus rule and a worked application together.

## First reviewed block: exponential and logarithm

The current source already supplies a factorial evaluator for every rational
input, a local self-derivative certificate on [-1,1], the unit exponential FTC,
agreement with repeated multiplication at one, logarithm-two series/rectangle
equivalence, and a finite square-substitution comparison. These existing results
were inspected in Lean 4.33.0-rc2 and their numerical evaluators were executed.
The general exp/log inverse discussion in the manuscript is broader than these
linked declarations. Do not present that entire chapter as a closed formal
package until the missing general-domain and inverse bridges are supplied.

## Next mathematical milestones

1. Complete positive-interval logarithm and bounded-interval exponential:
   derivative, scaling/addition, inverse laws, real powers. Each theorem needs
   the native construction and an exact-statement Mathlib comparison. Start
   with the existing successful local exponential and reciprocal quadratures.
2. Turn finite Taylor bounds into usable local approximation: polynomial and
   exponential examples, explicit remainder, composition on certified ranges,
   and range reduction. Report precision and operation cost, not just proof LOC.
3. First-order evolution: y'=ay and y'=ay+b, rational coefficients and initial
   data, a finite evaluator, an error bound and a uniqueness argument with
   explicit interval hypotheses. Continue to small matrix systems only after
   these applications are complete.
4. Complex exponential and oscillation: identify the computable series with
   the existing geometric sine/cosine, then use it for the harmonic oscillator.
   Preserve the arctangent construction rather than silently replacing it.
5. Improper integrals and transforms through applications: exponential tails,
   Gaussian evaluation, then finite Fourier calculations with explicit tails.
   This also advances the Chapter 1 pi catalogue.

Monotone and finite-piece constructions are the default tools, not a claim
that arbitrary functions admit a finite monotonicity partition. Add a local
extension only when a concrete application needs it. Finitely many corners
can be handled when encountered; do not make the Cantor-function boundary the
next development project.

## Chapter acceptance

The narrative gives the mathematical construction, a quantitative estimate,
a useful result and a worked calculation. The theorem-side map contains exact
checked declarations and actual dependency witnesses. A Mathlib route counts
only after it proves the SAME native proposition via independently established
bridges. Keep unfinished routes visible without assigning placeholder scores.
Compare full proof cost and additional cost beyond preceding chapters; count
shared arithmetic once. Protect Chapters 1 and 2 and the existing pi gallery.
