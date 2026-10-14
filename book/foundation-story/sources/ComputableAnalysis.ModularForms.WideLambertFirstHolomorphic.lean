import ComputableAnalysis.ModularForms.WideLambertFirstDerivative
import ComputableAnalysis.ModularForms.WideLambertFifthHolomorphic
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Exact slope-prefix agreement for actual wider-disk finite prefix derivatives. -/
theorem wideLambertFirstPrefix_derivative_agreement (q : Scalar) (hq : wideLambertFifthDomain q) (N : Nat) :
    ((wideLambertPrefixMap_holomorphic 1 N).derivative q hq).val.Equiv
      (ScalarSeries.block (fun n => (wideLambertFirstSlopeTerm q (LocalODE.interior_bound _ q hq) n).val) 0 N) := by
  have h := ScalarSeries.block_congr
    (fun n => ((wideWeightedLambertMap_holomorphic 1 n).derivative q hq).val)
    (fun n => (wideLambertFirstSlopeTerm q (LocalODE.interior_bound _ q hq) n).val)
    (fun n => wideWeightedLambertMap_derivative_slope 1 n q hq) 0 N
  exact equiv_trans ((wideLambertPrefixMap_holomorphic 1 N).derivative q hq).property
    (ScalarSeries.block_valid _ (fun n => ((wideWeightedLambertMap_holomorphic 1 n).derivative q hq).property) 0 N)
    (ScalarSeries.block_valid _ (fun n => (wideLambertFirstSlopeTerm q (LocalODE.interior_bound _ q hq) n).property) 0 N)
    (wideLambertPrefixMap_derivative 1 N q hq) h

/-- Uniform convergence to actual prefix derivatives, rather than only formal slope sums. -/
theorem wideLambertFirstSlopeValue_close_actual_derivative (q : Scalar) (hq : wideLambertFifthDomain q) (N : Nat) :
    Small (sub (wideLambertFirstSlopeValue q (LocalODE.interior_bound _ q hq)).val
      ((wideLambertPrefixMap_holomorphic 1 N).derivative q hq).val) (128*((1:Rat)/8)^N) := by
  exact Small.congr
    (sub_valid (wideLambertFirstSlopeValue q (LocalODE.interior_bound _ q hq)).property
      (ScalarSeries.block_valid _ (fun n => (wideLambertFirstSlopeTerm q (LocalODE.interior_bound _ q hq) n).property) 0 N))
    (sub_valid (wideLambertFirstSlopeValue q (LocalODE.interior_bound _ q hq)).property
      ((wideLambertPrefixMap_holomorphic 1 N).derivative q hq).property)
    (FunctionTheory.sub_congr (equiv_refl _ (wideLambertFirstSlopeValue q (LocalODE.interior_bound _ q hq)).property)
      (equiv_symm (wideLambertFirstPrefix_derivative_agreement q hq N)))
    (wideLambertFirstSlopeValue_close_prefix q (LocalODE.interior_bound _ q hq) N)

noncomputable def wideLambertFirstSlope_continuous :
    ContinuousOn wideLambertFifthDomain (fun q hq => wideLambertFirstSlopeValue q (LocalODE.interior_bound _ q hq)) :=
  continuousOn_of_uniform_prefixes (fun q hq => wideLambertFirstSlopeValue q (LocalODE.interior_bound _ q hq))
    (fun N q hq => (wideLambertPrefixMap_holomorphic 1 N).derivative q hq)
    (fun N => (wideLambertPrefixMap_holomorphic 1 N).continuousDerivative)
    (fun N => 128*((1:Rat)/8)^N) wideLambertFirstSlopeValue_tail_shrinks
    (fun N q hq => wideLambertFirstSlopeValue_close_actual_derivative q hq N)

/-- Actual holomorphicity of the executable wider Lambert evaluator. -/
noncomputable def wideLambertFirstMap_holomorphic : Holomorphic wideLambertFirstMap where
  openDomain := ⟨wideLambertFifthDomain_openData.radius,wideLambertFifthDomain_openData.inside⟩
  derivative q hq := wideLambertFirstSlopeValue q (LocalODE.interior_bound _ q hq)
  atPoint := wideLambertFirstMap_hasDerivativeAt
  derivative_congr q w hq hw he := wideLambertFirstSlopeValue_congr q w
    (LocalODE.interior_bound _ q hq) (LocalODE.interior_bound _ w hw) he
  continuousDerivative := wideLambertFirstSlope_continuous
end ComputableAnalysis.ModularForms
