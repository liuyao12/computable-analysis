import ComputableAnalysis.ExponentialComputations.API
import ComputableAnalysis.ComplexExponentialRealBridge

/-! Compatibility of the function API with the repository's computed e. -/
namespace ComputableAnalysis.ExponentialComputations
open ComplexRaw FunctionTheory RiemannHilbert ModularForms

theorem exp_one_equiv_ePowerSeries : (exp oneInput.val).val.Equiv ePowerSeries := by
  have h := entireExponential_legacy_rational (QComplex.ofRat 1) 1
    (by decide +kernel) (by decide +kernel)
  have hh := ComplexExponentialApproximation.exponentialRawAt_realPart_equiv_expPowerSeries 1 1
    (by decide +kernel) (by decide +kernel)
  exact RealRaw.equiv_trans (exp oneInput.val).property
    (realPart_valid (ComplexExponentialApproximation.exponentialRawAt_valid
      (z := QComplex.ofRat 1) (C := 1) (by decide +kernel) (by decide +kernel)))
    ExpProofs.ePowerSeries_valid (realPart_equiv h) hh

theorem exp_one_equiv_eCompoundInterest : (exp oneInput.val).val.Equiv eCompoundInterest :=
  RealRaw.equiv_trans (exp oneInput.val).property ExpProofs.ePowerSeries_valid ExpProofs.eCompoundInterest_valid
    exp_one_equiv_ePowerSeries ExpProofs.ePowerSeries_equiv_eCompoundInterest
end ComputableAnalysis.ExponentialComputations
