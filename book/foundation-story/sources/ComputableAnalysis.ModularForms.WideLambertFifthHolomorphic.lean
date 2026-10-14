import ComputableAnalysis.ModularForms.WideLambertPrefixHolomorphic
import ComputableAnalysis.RiemannHilbert.DomainUniformLimitContinuity
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- The actual finite-term derivative equals its independently constructed literal slope. -/
theorem wideWeightedLambertMap_derivative_slope (k n : Nat) (q : Scalar) (hq : wideLambertFifthDomain q) :
    ((wideWeightedLambertMap_holomorphic k n).derivative q hq).val.Equiv
      (weightedLambertSlope q (1/64) k (by decide +kernel) (by decide +kernel)
        (LocalODE.interior_bound _ q hq) n).val := by
  have h1 := wideWeightedLambertMap_derivative k n q hq
  have h2 := scaleRat_equiv (r := (((n+1:Nat):Rat)^k)) (wideLambertPowerMap_derivative n q hq)
  have h3 := weightedLambertSlope_wide_composition q (1/64) k
    (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ q hq) n
  exact equiv_trans ((wideWeightedLambertMap_holomorphic k n).derivative q hq).property
    (scaleRat_valid ((wideLambertPowerMap_holomorphic n).derivative q hq).property)
    (weightedLambertSlope q (1/64) k (by decide +kernel) (by decide +kernel)
      (LocalODE.interior_bound _ q hq) n).property h1
    (equiv_trans (scaleRat_valid ((wideLambertPowerMap_holomorphic n).derivative q hq).property)
      (scaleRat_valid (mul_valid
        (lambertDiskDerivative (nomePowerScalar q n) (nomePowerRadius (1/64) n)
          (nomePowerRadius_nonneg _ (by decide +kernel) n) (nomePowerRadius_local _ (by decide +kernel) (by decide +kernel) n)
          (nomePowerScalar_small q _ (by decide +kernel) (LocalODE.interior_bound _ q hq) n)).property
        ((tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (n+1)).derivative q trivial).property))
      (weightedLambertSlope q (1/64) k (by decide +kernel) (by decide +kernel)
        (LocalODE.interior_bound _ q hq) n).property h2 (equiv_symm h3))

/-- Exact slope-prefix agreement for actual wider-disk finite prefix derivatives. -/
theorem wideLambertFifthPrefix_derivative_agreement (q : Scalar) (hq : wideLambertFifthDomain q) (N : Nat) :
    ((wideLambertPrefixMap_holomorphic 5 N).derivative q hq).val.Equiv
      (ScalarSeries.block (fun n => (wideLambertFifthSlopeTerm q (LocalODE.interior_bound _ q hq) n).val) 0 N) := by
  have h := ScalarSeries.block_congr
    (fun n => ((wideWeightedLambertMap_holomorphic 5 n).derivative q hq).val)
    (fun n => (wideLambertFifthSlopeTerm q (LocalODE.interior_bound _ q hq) n).val)
    (fun n => wideWeightedLambertMap_derivative_slope 5 n q hq) 0 N
  exact equiv_trans ((wideLambertPrefixMap_holomorphic 5 N).derivative q hq).property
    (ScalarSeries.block_valid _ (fun n => ((wideWeightedLambertMap_holomorphic 5 n).derivative q hq).property) 0 N)
    (ScalarSeries.block_valid _ (fun n => (wideLambertFifthSlopeTerm q (LocalODE.interior_bound _ q hq) n).property) 0 N)
    (wideLambertPrefixMap_derivative 5 N q hq) h

/-- Uniform convergence to actual prefix derivatives, rather than only formal slope sums. -/
theorem wideLambertFifthSlopeValue_close_actual_derivative (q : Scalar) (hq : wideLambertFifthDomain q) (N : Nat) :
    Small (sub (wideLambertFifthSlopeValue q (LocalODE.interior_bound _ q hq)).val
      ((wideLambertPrefixMap_holomorphic 5 N).derivative q hq).val) (2048*((1:Rat)/4)^N) := by
  exact Small.congr
    (sub_valid (wideLambertFifthSlopeValue q (LocalODE.interior_bound _ q hq)).property
      (ScalarSeries.block_valid _ (fun n => (wideLambertFifthSlopeTerm q (LocalODE.interior_bound _ q hq) n).property) 0 N))
    (sub_valid (wideLambertFifthSlopeValue q (LocalODE.interior_bound _ q hq)).property
      ((wideLambertPrefixMap_holomorphic 5 N).derivative q hq).property)
    (FunctionTheory.sub_congr (equiv_refl _ (wideLambertFifthSlopeValue q (LocalODE.interior_bound _ q hq)).property)
      (equiv_symm (wideLambertFifthPrefix_derivative_agreement q hq N)))
    (wideLambertFifthSlopeValue_close_prefix q (LocalODE.interior_bound _ q hq) N)

noncomputable def wideLambertFifthSlope_continuous :
    ContinuousOn wideLambertFifthDomain (fun q hq => wideLambertFifthSlopeValue q (LocalODE.interior_bound _ q hq)) :=
  continuousOn_of_uniform_prefixes (fun q hq => wideLambertFifthSlopeValue q (LocalODE.interior_bound _ q hq))
    (fun N q hq => (wideLambertPrefixMap_holomorphic 5 N).derivative q hq)
    (fun N => (wideLambertPrefixMap_holomorphic 5 N).continuousDerivative)
    (fun N => 2048*((1:Rat)/4)^N) wideLambertFifthSlopeValue_tail_shrinks
    (fun N q hq => wideLambertFifthSlopeValue_close_actual_derivative q hq N)

/-- Actual holomorphicity of the executable wider Lambert evaluator. -/
noncomputable def wideLambertFifthMap_holomorphic : Holomorphic wideLambertFifthMap where
  openDomain := ⟨wideLambertFifthDomain_openData.radius,wideLambertFifthDomain_openData.inside⟩
  derivative q hq := wideLambertFifthSlopeValue q (LocalODE.interior_bound _ q hq)
  atPoint := wideLambertFifthMap_hasDerivativeAt
  derivative_congr q w hq hw he := wideLambertFifthSlopeValue_congr q w
    (LocalODE.interior_bound _ q hq) (LocalODE.interior_bound _ w hw) he
  continuousDerivative := wideLambertFifthSlope_continuous
end ComputableAnalysis.ModularForms
