import Lean
import ComputableAnalysis.RationalPrimitiveExamples

open Lean Elab Command

run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if mod.toString.startsWith "Mathlib" then
      throwError "Unexpected Mathlib import: {mod}"
  for root in [
      ``ComputableAnalysis.ComputableCoefficient.widthStage_spec,
      ``ComputableAnalysis.PrimitiveLogarithmEstimates.prefix_lipschitz,
      ``ComputableAnalysis.PrimitiveLogarithmEstimates.kernel_lipschitz,
      ``ComputableAnalysis.PrimitiveLogarithmEstimates.prefix_affine_secant,
      ``ComputableAnalysis.ComputableLogarithmChart.Coefficient.value_valid,
      ``ComputableAnalysis.ComputableLogarithmChart.Coefficient.derivative_valid,
      ``ComputableAnalysis.ComputableLogarithmChart.Coefficient.hasDerivative,
      ``ComputableAnalysis.ComputableLogarithmChart.simplePole_hasDerivative,
      ``ComputableAnalysis.ComputableLogarithmChart.simplePole_derivative_equiv,
      ``ComputableAnalysis.ComputableLogarithmChart.arctan_hasDerivative,
      ``ComputableAnalysis.ComputableLogarithmChart.arctan_derivative_equiv,
      ``ComputableAnalysis.ComputableLogarithmChart.arctan_valueSample,
      ``ComputableAnalysis.ComputableLogarithmChart.Coefficient.weightedValue_valid,
      ``ComputableAnalysis.ComputableLogarithmChart.Coefficient.weightedDerivative_valid,
      ``ComputableAnalysis.ComputableLogarithmChart.Coefficient.weightedHasDerivative,
      ``ComputableAnalysis.ComputableLogarithmChart.quadraticLog_hasDerivative,
      ``ComputableAnalysis.ComputableLogarithmChart.quadraticLog_derivative_equiv,
      ``ComputableAnalysis.ComputableLogarithmChart.quadraticArctan_hasDerivative,
      ``ComputableAnalysis.ComputableLogarithmChart.quadraticArctan_derivative_equiv,
      ``ComputableAnalysis.ComputablePrimitiveDerivativeExamples.irrationalPole_hasDerivative,
      ``ComputableAnalysis.ComputablePrimitiveDerivativeExamples.irrationalPole_derivative_is_reciprocal,
      ``ComputableAnalysis.ComputablePrimitiveDerivativeExamples.irrationalArctan_hasDerivative,
      ``ComputableAnalysis.ComputablePrimitiveDerivativeExamples.irrationalArctan_derivative_is_kernel,
      ``ComputableAnalysis.ComputablePrimitiveDerivativeExamples.irrationalArctan_series,
      ``ComputableAnalysis.ComputablePrimitiveDerivativeExamples.irrationalQuadratic_hasDerivative,
      ``ComputableAnalysis.ComputablePrimitiveDerivativeExamples.irrationalQuadratic_derivative_is_reciprocal,

      ``ComputableAnalysis.ComputableCoefficient.Value.equiv_of_samples,
      ``ComputableAnalysis.ComputableCoefficient.Expr.realize,
      ``ComputableAnalysis.ComputableCoefficient.Expr.realize_equiv,
      ``ComputableAnalysis.ComputableFactoredAlgebra.shadow_normalForm,
      ``ComputableAnalysis.ComputableFactoredAlgebra.Formula.sample_formalDerivative,
      ``ComputableAnalysis.ComputableFactoredAlgebra.requirements_sufficient,
      ``ComputableAnalysis.ComputableFactoredAlgebra.certifyFactors,
      ``ComputableAnalysis.ComputableFactoredAlgebra.primitive_correct,
      ``ComputableAnalysis.ComputableFactoredAlgebra.FactoredRational.primitive_correct,
      ``ComputableAnalysis.ComputablePrimitiveExamples.factors_checked,
      ``ComputableAnalysis.ComputablePrimitiveExamples.derivative_computes,
      ``ComputableAnalysis.ComputablePrimitiveExamples.integrand_computes,
      ``ComputableAnalysis.ComputablePrimitiveExamples.irrational_primitive_correct,
      ``ComputableAnalysis.ComputablePrimitiveExamples.zero_inverse_rejected,
      ``ComputableAnalysis.ComputablePrimitiveExamples.duplicate_irrational_pole_rejected,

      ``ComputableAnalysis.RationalFactoredPrimitives.generalQuadratic_value,
      ``ComputableAnalysis.RationalQuadraticDivision.divide_identity,
      ``ComputableAnalysis.RationalQuadraticDivision.norm_pos,
      ``ComputableAnalysis.RationalQuadraticDivision.nextNumerator_identity,
      ``ComputableAnalysis.RationalQuadraticDivision.remove_identity,
      ``ComputableAnalysis.RationalFactoredPrimitives.normalForm_identity,
      ``ComputableAnalysis.RationalFactoredPrimitives.decomposition,
      ``ComputableAnalysis.RationalFactoredPrimitives.Factorization.decomposition,
      ``ComputableAnalysis.RationalFactoredPrimitives.Factorization.primitive_correct,
      ``ComputableAnalysis.RationalPrimitiveExamples.mixedQuadratic_coefficients,
      ``ComputableAnalysis.RationalPrimitiveExamples.duplicateQuadratic_rejected,
      ``ComputableAnalysis.RationalPrimitiveExamples.factoredQuadraticExample_primitive,

      ``ComputableAnalysis.HasDerivativeOnInterval.scale,
      ``ComputableAnalysis.HasDerivativeOnInterval.linearCombination,
      ``ComputableAnalysis.RationalPrimitivePowers.hasDerivative,
      ``ComputableAnalysis.RationalPrimitivePowers.weighted_hasDerivative,
      ``ComputableAnalysis.RationalPartialFractions.decomposition,
      ``ComputableAnalysis.RationalPartialFractions.ofFactorization,
      ``ComputableAnalysis.RationalPrimitiveAssembly.radius_pos,
      ``ComputableAnalysis.RationalPrimitiveAssembly.denominator_near,
      ``ComputableAnalysis.RationalPrimitiveAssembly.splitPrimitive,
      ``ComputableAnalysis.RationalPrimitiveAssembly.ofFactorization,
      ``ComputableAnalysis.RationalPrimitiveExamples.automaticMixed_coefficients,
      ``ComputableAnalysis.RationalPrimitiveExamples.negativeTriplePole_hasDerivative,
      ``ComputableAnalysis.RationalPrimitiveExamples.automaticMixed_hasDerivative,
      ``ComputableAnalysis.RationalPrimitiveExamples.automaticMixed_elementary,
      ``ComputableAnalysis.RationalPrimitiveExamples.automaticMixed_radius,

      ``ComputableAnalysis.HasDerivativeOnInterval.add,
      ``ComputableAnalysis.RationalPrimitiveExamples.polynomialPlusLog_hasDerivative,
      ``ComputableAnalysis.RationalPrimitivePolynomial.hasDerivative,
      ``ComputableAnalysis.RationalPrimitivePolynomial.primitiveSum_zero,
      ``ComputableAnalysis.RationalPrimitiveLogarithm.logOnePlus_valid,
      ``ComputableAnalysis.RationalPrimitiveLogarithm.hasDerivative,
      ``ComputableAnalysis.RationalPrimitiveLogarithm.affineHasDerivative,
      ``ComputableAnalysis.RationalPrimitiveLogarithm.simplePole_hasDerivative,
      ``ComputableAnalysis.RationalPrimitiveLogarithm.poleRadius_pos,
      ``ComputableAnalysis.RationalPrimitiveExamples.negativePole_hasDerivative,
      ``ComputableAnalysis.RationalPrimitiveExamples.polynomial_hasDerivative,
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
  logInfo "ANALYTIC: every rational polynomial on every rational interval; every rationally split denominator near each permitted rational center; executable partial fractions and elementary evaluators, with actual derivative certificates."
  logInfo "FACTORIZATION: supplied computable-real linear and positive quadratic factors; interval-certified separation; computed partial fractions and represented formal-derivative equivalence; irrational regression checked."
  logInfo "CONCRETE: computable-coefficient logarithm and arctangent finite secant certificates; weighted quadratic base primitives; irrational pole and quadratic reciprocal bridges."
  logInfo "SCOPE: factorization existence, analytic assembly for computable coefficients, and represented trigonometric transport remain open."

#print axioms ComputableAnalysis.RationalPrimitiveFormula.Decomposition.primitive_correct
#print axioms ComputableAnalysis.TrigonometricRationalization.Expr.pullback_correct

#check ComputableAnalysis.RationalPrimitiveFormula.Decomposition.primitive_correct
#check ComputableAnalysis.TrigonometricRationalization.Expr.pullback_correct
#check ComputableAnalysis.TrigonometricRationalization.rational_circle_chart_cover

#check ComputableAnalysis.RationalPrimitivePolynomial.hasDerivative
#check ComputableAnalysis.RationalPrimitiveLogarithm.simplePole_hasDerivative
