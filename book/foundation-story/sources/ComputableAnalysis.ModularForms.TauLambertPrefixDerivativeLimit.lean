import ComputableAnalysis.ModularForms.TauLambertSlopeAgreement
import ComputableAnalysis.ModularForms.TauLambertSlopeSeries
import ComputableAnalysis.ModularForms.TauLambertPrefixHolomorphic

/-! Exact slope-prefix agreement and uniform actual derivative convergence. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem tauLambertPrefixDerivative_slope_agreement (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) :
    ((tauLambertPrefixMap_holomorphic 1 N).derivative q hq).val.Equiv
      (tauLambertSlopePrefix q hq N).val := by
  have h := ScalarSeries.block_congr
    (fun n => ((tauWeightedLambertMap_holomorphic 1 n).derivative q hq).val)
    (fun n => (weightedLambertOneSlope q (1/1024) (by decide +kernel) (by decide +kernel)
      (LocalODE.interior_bound _ q hq) n).val)
    (fun n => weightedLambertOneSlope_actual q hq n) 0 N
  exact equiv_trans ((tauLambertPrefixMap_holomorphic 1 N).derivative q hq).property
    (ScalarSeries.block_valid _ (fun n => ((tauWeightedLambertMap_holomorphic 1 n).derivative q hq).property) 0 N)
    (tauLambertSlopePrefix q hq N).property (tauLambertPrefixMap_derivative 1 N q hq) h

/-- Uniform geometric convergence of actual finite-prefix derivatives. -/
theorem tauLambertSlopeValue_close_actual_derivative (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) :
    Small (sub (tauLambertSlopeValue q hq).val
      ((tauLambertPrefixMap_holomorphic 1 N).derivative q hq).val) (128*(1/128:Rat)^N) := by
  exact Small.congr
    (sub_valid (tauLambertSlopeValue q hq).property (tauLambertSlopePrefix q hq N).property)
    (sub_valid (tauLambertSlopeValue q hq).property ((tauLambertPrefixMap_holomorphic 1 N).derivative q hq).property)
    (FunctionTheory.sub_congr (equiv_refl _ (tauLambertSlopeValue q hq).property)
      (equiv_symm (tauLambertPrefixDerivative_slope_agreement q hq N)))
    (tauLambertSlopeValue_close_prefix q hq N)

end ComputableAnalysis.ModularForms
