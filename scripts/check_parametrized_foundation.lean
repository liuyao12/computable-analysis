import Lean
import ComputableAnalysis.ParametrizedFoundationExamples
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if mod.toString.startsWith "Mathlib" then
      throwError "Unexpected Mathlib import: {mod}"
  for root in [``ComputableAnalysis.RawLimit.HasEnclosureValue.unique,
      ``ComputableAnalysis.RawLimit.HasEnclosureValue.congr_value,
      ``ComputableAnalysis.RawLimit.parametrizedLimit_iff,
      ``ComputableAnalysis.RawLimit.HasParametrizedLimit.unique,
      ``ComputableAnalysis.RawLimit.alternating_no_parametrizedLimit,
      ``ComputableAnalysis.RawLimit.prefix_valid,
      ``ComputableAnalysis.RawLimit.prefix_hasEnclosureValue,
      ``ComputableAnalysis.RawLimit.enclosureValue_iff,
      ``ComputableAnalysis.BracketDerivative.hasDerivative_iff_secantLimits,
      ``ComputableAnalysis.BracketDerivative.outerDerivative_hasDerivative,
      ``ComputableAnalysis.BracketContinuity.unique,
      ``ComputableAnalysis.BracketContinuity.bracket_values_equiv,
      ``ComputableAnalysis.BracketContinuity.exists_continuousAt_of_enclosures,
      ``ComputableAnalysis.BracketContinuity.congr_point,
      ``ComputableAnalysis.BracketContinuity.congr_value,
      ``ComputableAnalysis.BracketContinuity.congr_function,
      ``ComputableAnalysis.BracketContinuity.hasContinuousAt_iff_neighborhoods,
      ``ComputableAnalysis.BracketContinuity.values_tendTo,
      ``ComputableAnalysis.BracketContinuity.rational_agreement,
      ``ComputableAnalysis.BracketContinuity.identity,
      ``ComputableAnalysis.BracketContinuity.constant,
      ``ComputableAnalysis.ScheduledIntervalRegularOn.bracketCandidate_hasEnclosureValue,
      ``ComputableAnalysis.ScheduledIntervalRegularOn.exists_continuousAt,
      ``ComputableAnalysis.IntervalRegularOn.continuousAt_closed,
      ``ComputableAnalysis.EpsilonDeltaContinuousOn.exists_continuousAt,
      ``ComputableAnalysis.HasDerivativeOnInterval.toParametrizedDerivative,
      ``ComputableAnalysis.FunctionTheory.ContinuousOn.hasEnclosureCoordinates,
      ``ComputableAnalysis.FunctionTheory.HasDerivativeAt.hasRemainderCoordinates,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.ContinuousOn.hasEnclosureCoordinates,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.HasDerivativeAt.hasRemainderCoordinates,
      ``ComputableAnalysis.ParametrizedFoundationExamples.square_continuous_closed,
      ``ComputableAnalysis.ParametrizedFoundationExamples.affine_finite_certificate,
      ``ComputableAnalysis.ParametrizedFoundationExamples.jump_not_continuous] do
    let axioms ← collectAxioms root
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {root}"
    logInfo m!"AUDIT {root}: {axioms}"
  logInfo "PASS: covered cofinal valid diagonals; limit compatibility; continuity uniqueness and invariance; independent bracket agreement; old interval and finite derivative adapters; complex coordinate and normalized remainder bridges; concrete affine and square applications; alternating-tail and jump rejection. Standard axioms only; no Mathlib imports."
