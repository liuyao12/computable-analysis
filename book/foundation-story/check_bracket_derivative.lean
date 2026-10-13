import Lean
import ComputableAnalysis.BracketDerivativeExamples
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if mod.toString.startsWith "Mathlib" then
      throwError "Unexpected Mathlib import: {mod}"
  for root in [``ComputableAnalysis.RawLimit.unique,
      ``ComputableAnalysis.RawLimit.congr_target_iff,
      ``ComputableAnalysis.RawLimit.congr_sequence,
      ``ComputableAnalysis.RawLimit.bisequence_unique,
      ``ComputableAnalysis.RawLimit.bisequence_congr_target,
      ``ComputableAnalysis.BracketDerivative.unique,
      ``ComputableAnalysis.BracketDerivative.congr_point_iff,
      ``ComputableAnalysis.BracketDerivative.congr_value_iff,
      ``ComputableAnalysis.BracketDerivative.congr_function,
      ``ComputableAnalysis.BracketDerivative.clipped_admissible,
      ``ComputableAnalysis.BracketDerivative.allowance_tendsTo_zero,
      ``ComputableAnalysis.BracketDerivative.outerDerivative_hasDerivative,
      ``ComputableAnalysis.BracketDerivativeExamples.squareDerivative_hasDerivative,
      ``ComputableAnalysis.BracketDerivativeExamples.square_closed_interval,
      ``ComputableAnalysis.BracketDerivativeExamples.affine_hasDerivative,
      ``ComputableAnalysis.BracketDerivativeExamples.affinePointwise_hasDerivative,
      ``ComputableAnalysis.BracketDerivativeExamples.squarePointwise_hasDerivative] do
    let axioms ← collectAxioms root
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {root}"
    logInfo m!"AUDIT {root}: {axioms}"
  logInfo m!"PASS: two-index limits and rational-endpoint derivatives; uniqueness and representation invariance; strictly positive domain-contained brackets; generic outer-secant bridge; old convex computation instantiated for square and for arbitrary represented affine coefficients. Standard axioms only; no Mathlib imports."
