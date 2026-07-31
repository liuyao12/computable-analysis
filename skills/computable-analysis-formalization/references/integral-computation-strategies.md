# Integral computation strategies

## Scope

Use this reference to formalize one definite integral as a finite rational
algorithm. The project does not define a global integral operator for all
bounded or continuous functions. A completed result is a specific evaluator,
its validity and rate certificate, and a theorem identifying that evaluator
with the displayed integral or endpoint expression.

Start with `ComputableAnalysis.Calculus`. Use
`Integral.ConstructionFor` as an interface for a particular construction,
not as evidence that an arbitrary integrand is integrable. Keep an endpoint
identity, a change-of-variables comparison, or another semantic bridge
separate from the raw interval computation.

## Select a construction

| Shape of the integrand | Construct | Typical proof obligation |
| --- | --- | --- |
| Exact derivative of a checked primitive | Endpoint difference plus a specific FTC certificate | Prove the finite derivative error and endpoint bridge |
| Monotone on one rational interval | `MonotoneConstructionFor` or `NondecreasingConstructionFor` | Prove the declared order and the rectangle-width schedule |
| Rational-Lipschitz on `[0,1]` | `IntegralIdentities.LipschitzDyadic` | Prove a rational Lipschitz constant and the dyadic error bound |
| Monotone on finitely many rational pieces | `PiecewiseMonotoneConstructionFor` | Prove order independently on every piece and combine their boxes |
| Finite monotone decomposition with non-rational turns | `TurningPointBracket` plus `TurningBracketIntegralCandidate` | Supply one shrinking rational bracket per turn, monotone-piece certificates, and a range bound for every gap |
| Substitution, symmetry, or integration by parts | A literal finite mesh comparison | Prove the finite algebra and error terms; do not cite a future general theorem |

Use the exact expression of the integrand in every construction. State where
denominators stay apart from zero and where a branch or sign condition holds.
Use an interval evaluator rather than endpoint samples when the function is
inexact.

## Build a finite turning-bracket computation

Use the following route for any supplied finite monotone decomposition.  A
one-turn picture is only the smallest illustration: every non-rational turn
uses the same component, and the finite stage sums all outer pieces and all
unresolved gaps.

1. List the finitely many monotone pieces and every non-rational turn between
   adjacent pieces.  Do not select a rational point merely to make a static
   partition.
2. For every turn, define `TurningPointBracket a b`. Its `raw` exposes the
   stagewise rational bracket `[ell_n, r_n]`; prove `raw.Valid`, containment
   in `[a,b]`, and shrinking width.
3. At stage `n`, construct every outer integral on the rational endpoints
   selected by its adjacent brackets.  Supply `MonotoneConstructionFor` for
   each restricted `FunctionOnInterval`; these constructions may depend on
   `n`.
4. Choose a fixed rational value interval `B=[L,U]` for every unresolved
   gap, and prove the corresponding pointwise range enclosure at every
   requested evaluator precision.
5. Give each gap the literal box `(r_n - ell_n) * B`. The checked theorem
   `turningPointMiddleBox_width` gives
   `width = (r_n - ell_n) * width(B)`.
6. Sum all monotone boxes and all gap boxes with
   `FinitePiecewiseStageAssembly`. Its checked finite arithmetic theorem gives
   the combined stage a shrinking width. The one-gap helper
   `TurningBracketIntegralCandidate` (implemented by the legacy
   `SingleTurnIntegralCandidate`) supplies reusable component boxes; the
   function-specific proof that the assembled boxes cover an intended integral
   is still required.
7. Use `middleBox_contained_symmetric` when a bound `B ⊆ [-K,K]` is
   available. It yields the sharper estimate
   `[-K*(r_n-ell_n), K*(r_n-ell_n)]` for that gap.

These seven steps build a numerical candidate. They do not yet prove that the
candidate boxes enclose an intended integral. Finish with
`TurningBracketIntegralCompletion`: give a valid anchor raw value, prove the
candidate is equivalent to that anchor, and give the stated anchor radius
schedule. The resulting `stabilizedRaw` has a checked validity proof while
its runtime still reads only the finite pieces belonging to that bracket.

## Prove the missing semantic comparison

Choose the comparison that matches the particular integrand:

- Compare the outer rectangles and middle range box with a pre-existing
  Darboux construction.
- Prove a finite partition identity when the turn is an algebraic or
  trigonometric change of variables.
- Prove an endpoint identity from a supplied derivative-bound FTC
  certificate.
- Refine both constructions to a common rational partition and bound the
  difference cell by cell.

State this comparison explicitly. Do not infer it from shrinking widths
alone: two independent shrinking raw computations need an overlap or
equivalence theorem to be identified.

## Check the result

- Expose a theorem for the literal stage computation.
- Prove every width factor is nonnegative before multiplying inequalities.
- Check the zero-width and positive-width cases separately when dividing by
  `width(B)`.
- Keep the actual rate in the public theorem or completion schedule.
- Document whether the result is a checked endpoint theorem, a reusable
  construction interface, or a remaining target.

## Common failures

- Calling a pointwise rational function integrable without a whole-interval
  denominator or range certificate.
- Assuming the turning point is rational or using a completed-real
  intermediate-value argument.
- Proving that a middle box shrinks but omitting a value bound that locates
  it.
- Reusing monotonicity across the unresolved bracket.
- Presenting a finite integration-by-parts or substitution identity as a
  general theorem before its partition-error argument exists.
