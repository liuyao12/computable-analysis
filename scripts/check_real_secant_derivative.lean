import Lean
import ComputableAnalysis.RealSecantDerivativeExamples
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if mod.toString.startsWith "Mathlib" then throwError "Unexpected Mathlib import: {mod}"
  for root in [
      ``ComputableAnalysis.RealSecantDerivative.flatBox_height,
      ``ComputableAnalysis.RealSecantDerivative.flat_compute,
      ``ComputableAnalysis.RealSecantDerivative.flat_imagPart,
      ``ComputableAnalysis.RealSecantDerivative.flat_equiv_iff,
      ``ComputableAnalysis.RealSecantDerivative.flat_enclosure_iff,
      ``ComputableAnalysis.RealSecantDerivative.hasDerivative_iff_flatBoxes,
      ``ComputableAnalysis.RealSecantDerivative.hasDerivative_iff_neighborhoods,
      ``ComputableAnalysis.RealSecantDerivative.HasDerivativeAt.bracket,
      ``ComputableAnalysis.RealSecantDerivative.unique,
      ``ComputableAnalysis.RealSecantDerivative.congr_point,
      ``ComputableAnalysis.RealSecantDerivative.congr_value,
      ``ComputableAnalysis.RealSecantDerivative.congr_function,
      ``ComputableAnalysis.RealSecantDerivative.restrict,
      ``ComputableAnalysis.RealSecantDerivative.HasDerivativeAt.negate,
      ``ComputableAnalysis.RealSecantDerivative.secant_neg_compute,
      ``ComputableAnalysis.RealSecantDerivative.secant_swap_compute,
      ``ComputableAnalysis.RealSecantDerivative.outerDerivative_hasDerivative,
      ``ComputableAnalysis.RealSecantDerivative.concave_outerDerivative_hasDerivative,
      ``ComputableAnalysis.RealSecantDerivativeExamples.squareDerivative_shrinkingBoxes,
      ``ComputableAnalysis.RealSecantDerivativeExamples.square_closed,
      ``ComputableAnalysis.RealSecantDerivativeExamples.affine_shrinkingBoxes,
      ``ComputableAnalysis.RealSecantDerivativeExamples.square_centered_shrinkingBoxes,
      ``ComputableAnalysis.RealSecantDerivativeExamples.affine_centered_shrinkingBoxes,
      ``ComputableAnalysis.RealSecantDerivativeExamples.negativeSquareDerivative_equiv,
      ``ComputableAnalysis.RealSecantDerivativeExamples.negativeSquareDerivative_valid,
      ``ComputableAnalysis.RealSecantDerivativeExamples.negativeSquare_secant_order,
      ``ComputableAnalysis.RealSecantDerivativeExamples.negativeSquareDerivative_shrinkingBoxes,
      ``ComputableAnalysis.RealSecantDerivativeExamples.negativeSquare_centered_shrinkingBoxes,
      ``ComputableAnalysis.RealSecantDerivativeExamples.affine_finite_shrinkingBoxes,
      ``ComputableAnalysis.HasDerivativeOnInterval.toShrinkingSecantDerivative] do
    let axioms ← collectAxioms root
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {root}"
    logInfo m!"AUDIT {root}: {axioms}"
  logInfo "PASS: all-pair shrinking real secant intervals and exact zero-height rectangle equivalence; uniqueness, input/output/function invariance, orientation and negation; convex and concave outer constructions; actual centered square, represented-coefficient affine and nonlinear concave square computations; closed-domain endpoints and finite derivative bridge. Standard axioms only; no Mathlib imports."
