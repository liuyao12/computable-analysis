import ComputableAnalysis.ModularForms.WideLambertThirdDerivative
import ComputableAnalysis.ModularForms.WideLambertFifthHolomorphic
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Exact slope-prefix agreement for actual wider-disk finite prefix derivatives. -/
theorem wideLambertThirdPrefix_derivative_agreement (q : Scalar) (hq : wideLambertFifthDomain q) (N : Nat) :
    ((wideLambertPrefixMap_holomorphic 3 N).derivative q hq).val.Equiv
      (ScalarSeries.block (fun n => (wideLambertThirdSlopeTerm q (LocalODE.interior_bound _ q hq) n).val) 0 N) := by
  have h := ScalarSeries.block_congr
    (fun n => ((wideWeightedLambertMap_holomorphic 3 n).derivative q hq).val)
    (fun n => (wideLambertThirdSlopeTerm q (LocalODE.interior_bound _ q hq) n).val)
    (fun n => wideWeightedLambertMap_derivative_slope 3 n q hq) 0 N
  exact equiv_trans ((wideLambertPrefixMap_holomorphic 3 N).derivative q hq).property
    (ScalarSeries.block_valid _ (fun n => ((wideWeightedLambertMap_holomorphic 3 n).derivative q hq).property) 0 N)
    (ScalarSeries.block_valid _ (fun n => (wideLambertThirdSlopeTerm q (LocalODE.interior_bound _ q hq) n).property) 0 N)
    (wideLambertPrefixMap_derivative 3 N q hq) h

/-- Uniform convergence to actual prefix derivatives, rather than only formal slope sums. -/
theorem wideLambertThirdSlopeValue_close_actual_derivative (q : Scalar) (hq : wideLambertFifthDomain q) (N : Nat) :
    Small (sub (wideLambertThirdSlopeValue q (LocalODE.interior_bound _ q hq)).val
      ((wideLambertPrefixMap_holomorphic 3 N).derivative q hq).val) (128*((1:Rat)/2)^N) := by
  exact Small.congr
    (sub_valid (wideLambertThirdSlopeValue q (LocalODE.interior_bound _ q hq)).property
      (ScalarSeries.block_valid _ (fun n => (wideLambertThirdSlopeTerm q (LocalODE.interior_bound _ q hq) n).property) 0 N))
    (sub_valid (wideLambertThirdSlopeValue q (LocalODE.interior_bound _ q hq)).property
      ((wideLambertPrefixMap_holomorphic 3 N).derivative q hq).property)
    (FunctionTheory.sub_congr (equiv_refl _ (wideLambertThirdSlopeValue q (LocalODE.interior_bound _ q hq)).property)
      (equiv_symm (wideLambertThirdPrefix_derivative_agreement q hq N)))
    (wideLambertThirdSlopeValue_close_prefix q (LocalODE.interior_bound _ q hq) N)

noncomputable def wideLambertThirdSlope_continuous :
    ContinuousOn wideLambertFifthDomain (fun q hq => wideLambertThirdSlopeValue q (LocalODE.interior_bound _ q hq)) :=
  continuousOn_of_uniform_prefixes (fun q hq => wideLambertThirdSlopeValue q (LocalODE.interior_bound _ q hq))
    (fun N q hq => (wideLambertPrefixMap_holomorphic 3 N).derivative q hq)
    (fun N => (wideLambertPrefixMap_holomorphic 3 N).continuousDerivative)
    (fun N => 128*((1:Rat)/2)^N) wideLambertThirdSlopeValue_tail_shrinks
    (fun N q hq => wideLambertThirdSlopeValue_close_actual_derivative q hq N)

/-- Actual holomorphicity of the executable wider Lambert evaluator. -/
noncomputable def wideLambertThirdMap_holomorphic : Holomorphic wideLambertThirdMap where
  openDomain := ⟨wideLambertFifthDomain_openData.radius,wideLambertFifthDomain_openData.inside⟩
  derivative q hq := wideLambertThirdSlopeValue q (LocalODE.interior_bound _ q hq)
  atPoint := wideLambertThirdMap_hasDerivativeAt
  derivative_congr q w hq hw he := wideLambertThirdSlopeValue_congr q w
    (LocalODE.interior_bound _ q hq) (LocalODE.interior_bound _ w hw) he
  continuousDerivative := wideLambertThirdSlope_continuous
end ComputableAnalysis.ModularForms
