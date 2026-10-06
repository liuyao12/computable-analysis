import ComputableAnalysis.ExponentialComputations.API
open ComputableAnalysis
open ComputableAnalysis.ExponentialComputations

#check compoundApproximation_error
#check compoundValue_equiv_powerSeries
#check Implementation.equivalent
#check Implementation.congr
#check representedTaylor_agrees
#check exp_positive
#check exp_injective
#check log_exp
#check exp_log
#check logChart_derivative
#check integralLog_hasIntegral
#check integralLog_equiv_log
#check integralLog_exp
#check exp_integralLog
#check integralLog_congr
#check real_computation_agrees_of_integral_inverse

#print axioms compoundValue_equiv_powerSeries
#print axioms Implementation.equivalent
#print axioms representedTaylor_agrees
#print axioms exp_positive
#print axioms exp_injective
#print axioms log_exp
#print axioms exp_log
#print axioms logChart_derivative
#print axioms integralLog_hasIntegral
#print axioms integralLog_equiv_log
#print axioms integralLog_exp
#print axioms exp_integralLog
#print axioms integralLog_congr
#print axioms real_computation_agrees_of_integral_inverse

/-- Literal finite compound-interest power, checked by kernel reduction. -/
example : ((compoundApproximation
    ⟨ComplexRaw.ofQComplex (QComplex.ofRat 1),ComplexRaw.ofQComplex_valid _⟩ 3).val.compute 0).lo.re =
    (625:Rat)/256 := by decide +kernel

/-- A real implementation comparison requires only validity of its input. -/
example (x : RealInput) :
    (compoundInterest.realEval x).val.Equiv (powerSeries.realEval x).val :=
  ComplexRaw.realPart_equiv (Implementation.equivalent compoundInterest powerSeries (realAxis x))
