# Computation certificate catalog

## Raw numbers and implementation agreement

Use `ComputableAnalysis.Basic` for `QInterval`, `RealRaw`,
`RealRaw.Valid`, and `RealRaw.Equiv`. Define an evaluator as rational boxes.
Prove endpoint order, nesting or an explicit stabilization route, and a
width modulus. Compare two definitions only after both have validity proofs.
Use overlap-based `RealRaw.Equiv`; never use a completed-real quotient as a
shortcut.

## Interval functions and domains

Use `FunctionOnInterval` for a rational closed domain. Start exact polynomial
or affine examples with `FunctionOnInterval.exactRat`. For a quotient, use
`RatFun` and prove `RatFun.DenominatorApartOnInterval`; pointwise
definedness does not exclude an irrational zero of a denominator.

Use `IntervalRegularOn` when a downstream theorem needs a genuine interval
enclosure or rational epsilon-delta continuity. Its
`epsilonDeltaContinuous` theorem is the project route to continuity without
an imported topology.

## Finite derivatives and endpoint formulas

Use `HasDerivativeOnInterval` or `HasForwardDerivativeAt` for rational
finite-difference certificates. Let evaluator precision depend on the
rational step when necessary. Keep a coefficient identity for a formal power
series distinct from an analytic derivative theorem for the corresponding
boxed function.

Use `FTC.EffectiveFTC`, `Integral.DefiniteIdentityFor`, or a dedicated
finite comparison only after providing the required integral construction.
A familiar primitive is a proposal to check, not an integral table entry.

## Series, exponential, and logarithm

Use `PowerSeries`, `Series`, and `ExpProofs` for a finite prefix plus a
rational tail majorant. State a rate in terms of the public raw evaluator.
Use raw-real equivalence to relate series, Euler products, or other
representations. Do not claim the scalar function identity or derivative
law for an elementary function until the matching interval-function
certificate is present.

Use `ElementaryFunctions` for positive-base and rational-power interfaces.
Retain the explicit obligation of rational-exponent continuity unless the
particular proof supplies it.

## Inverse and algebraic branches

Use `Extension` and `AlgebraicFunctions` for monotone inverse branches.
Supply range, separation, and bisection data instead of selecting a real
root. Treat square roots, inverse trigonometric branches, and logarithms as
represented computations with branch hypotheses.

## Linear ODEs

Use `PeanoBaker` for sampled systems, chronological products, finite
variation of constants, and finite uniqueness. State the discrete recurrence
first. For a continuous theorem, add component interval integration and an
explicit factorial-tail schedule; the finite core alone does not prove
continuous Picard--Lindelof.

## Pi as an integration suite

Use `PiProofs.PiCoverageBridge` only to register an end-to-end independent
bridge. Present normal mathematics in the blueprint: an integral evaluation,
a series theorem, or a geometric formula. Treat Pi agreement as a regression
test for distinct capability families, not as the overall calculus score.

## Required publication record

Update the source module, `blueprint/lean_decls`, a natural-language
blueprint chapter, `GOALS.md`, and `FORMALIZATION_GUIDE.md` when a new
checked public capability is added. State an actual convergence-rate theorem
where the construction has one. Run the no-import/no-placeholder audit before
publishing.
