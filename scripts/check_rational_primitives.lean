import Lean
import ComputableAnalysis.RationalPrimitiveExamples

open Lean Elab Command

run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if mod.toString.startsWith "Mathlib" then
      throwError "Unexpected Mathlib import: {mod}"
  for root in [
      ``ComputableAnalysis.RationalExpressionNormalization.compile_correct,
      ``ComputableAnalysis.RationalPrimitiveFormula.quadraticPrimitive_correct,
      ``ComputableAnalysis.RationalPrimitiveFormula.NormalForm.primitive_correct,
      ``ComputableAnalysis.RationalPrimitiveFormula.Decomposition.primitive_correct,
      ``ComputableAnalysis.RationalPrimitiveFormula.Decomposition.primitive_regular,
      ``ComputableAnalysis.TrigonometricRationalization.Expr.pullback_correct,
      ``ComputableAnalysis.TrigonometricRationalization.Expr.pullback_defined_iff,
      ``ComputableAnalysis.TrigonometricRationalization.circle_identity,
      ``ComputableAnalysis.TrigonometricRationalization.recover_parameter,
      ``ComputableAnalysis.TrigonometricRationalization.rational_circle_chart_cover,
      ``ComputableAnalysis.TrigonometricRationalization.Expr.antipodal_pullback_correct,
      ``ComputableAnalysis.RationalPrimitiveExamples.twoPoles_primitive,
      ``ComputableAnalysis.RationalPrimitiveExamples.repeatedQuadratic_derivative,
      ``ComputableAnalysis.RationalPrimitiveExamples.doubleInverse_undefined,
      ``ComputableAnalysis.RationalPrimitiveExamples.zeroTimesPole_undefined,
      ``ComputableAnalysis.RationalPrimitiveExamples.onePlusCosine_pullback,
      ``ComputableAnalysis.RationalPrimitiveExamples.cosecant_pullback_pole,
      ``ComputableAnalysis.RationalPrimitiveExamples.zeroDenominator_pullback] do
    let axioms ← collectAxioms root
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {root}: {ax}"
    logInfo m!"CHECKED {root}"
  logInfo "PASS: rational primitive algebra; domain-preserving circle pullback; no Mathlib, native-decision axioms, or unfinished proofs; standard Lean logical axioms only."
  logInfo "SCOPE: formal derivatives of supplied rational partial fractions; general decomposition and analytic realization remain open."

#print axioms ComputableAnalysis.RationalPrimitiveFormula.Decomposition.primitive_correct
#print axioms ComputableAnalysis.TrigonometricRationalization.Expr.pullback_correct

#check ComputableAnalysis.RationalPrimitiveFormula.Decomposition.primitive_correct
#check ComputableAnalysis.TrigonometricRationalization.Expr.pullback_correct
#check ComputableAnalysis.TrigonometricRationalization.rational_circle_chart_cover
