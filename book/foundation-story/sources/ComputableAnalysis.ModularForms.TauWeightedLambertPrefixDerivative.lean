import ComputableAnalysis.ModularForms.TauWeightedLambertSlope
import ComputableAnalysis.ModularForms.TauWeightedLambertSlopeSeries
import ComputableAnalysis.ModularForms.TauLambertPrefixHolomorphic

/-! Exact slope-prefix agreement and uniform actual derivative convergence. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem tauWeightedLambertPrefixDerivative_slope_agreement (q : Scalar) (hq : tauEulerNomeDomain q) (k : Nat) (hk : k≤5) (N : Nat) :
    ((tauLambertPrefixMap_holomorphic k N).derivative q hq).val.Equiv
      (tauWeightedLambertSlopePrefix q hq k hk N).val := by
  have h := ScalarSeries.block_congr
    (fun n => ((tauWeightedLambertMap_holomorphic k n).derivative q hq).val)
    (fun n => (weightedLambertSlope q (1/1024) k (by decide +kernel) (by decide +kernel)
      (LocalODE.interior_bound _ q hq) n).val)
    (fun n => tauWeightedLambertSlope_actual q hq k n) 0 N
  exact equiv_trans ((tauLambertPrefixMap_holomorphic k N).derivative q hq).property
    (ScalarSeries.block_valid _ (fun n => ((tauWeightedLambertMap_holomorphic k n).derivative q hq).property) 0 N)
    (tauWeightedLambertSlopePrefix q hq k hk N).property (tauLambertPrefixMap_derivative k N q hq) h

/-- Uniform geometric convergence of actual finite-prefix derivatives. -/
theorem tauWeightedLambertSlopeValue_close_actual_derivative (q : Scalar) (hq : tauEulerNomeDomain q) (k : Nat) (hk : k≤5) (N : Nat) :
    Small (sub (tauWeightedLambertSlopeValue q hq k hk).val
      ((tauLambertPrefixMap_holomorphic k N).derivative q hq).val) (128*(weightedSlopeRatio k)^N) := by
  exact Small.congr
    (sub_valid (tauWeightedLambertSlopeValue q hq k hk).property (tauWeightedLambertSlopePrefix q hq k hk N).property)
    (sub_valid (tauWeightedLambertSlopeValue q hq k hk).property ((tauLambertPrefixMap_holomorphic k N).derivative q hq).property)
    (FunctionTheory.sub_congr (equiv_refl _ (tauWeightedLambertSlopeValue q hq k hk).property)
      (equiv_symm (tauWeightedLambertPrefixDerivative_slope_agreement q hq k hk N)))
    (tauWeightedLambertSlopeValue_close_prefix q hq k hk N)

end ComputableAnalysis.ModularForms
