import ComputableAnalysis.ModularForms.TauLambertPrefixDerivativeLimit
import ComputableAnalysis.ModularForms.TauLambertContinuity
import ComputableAnalysis.ModularForms.TauWeightTwoNomeMap
import ComputableAnalysis.RiemannHilbert.DomainUniformLimitContinuity

/-! Actual Lambert value and continuous derivative-candidate maps. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def tauLambertNomeMap : DomainFunctions.Map where
  domain := tauEulerNomeDomain
  eval := tauLambertValue
  domain_congr := tauEulerNomeDomain_openData.invariant
  eval_congr := tauLambertValue_congr

def tauLambertSlopeMap : DomainFunctions.Map where
  domain := tauEulerNomeDomain
  eval := tauLambertSlopeValue
  domain_congr := tauEulerNomeDomain_openData.invariant
  eval_congr := tauLambertSlopeValue_congr

/-- Continuity of the constructed derivative candidate follows from actual prefixes. -/
noncomputable def tauLambertSlopeMap_continuous :
    ContinuousOn tauLambertSlopeMap.domain tauLambertSlopeMap.eval :=
  continuousOn_of_uniform_prefixes tauLambertSlopeValue
    (fun N q hq => (tauLambertPrefixMap_holomorphic 1 N).derivative q hq)
    (fun N => (tauLambertPrefixMap_holomorphic 1 N).continuousDerivative)
    (fun N => 128*(1/128:Rat)^N) tauLambertSlopeSeries_tail_shrinks
    (fun N q hq => tauLambertSlopeValue_close_actual_derivative q hq N)

/-- The actual infinite Lambert value has its already constructed continuity modulus. -/
def tauLambertNomeMap_continuous : ContinuousOn tauLambertNomeMap.domain tauLambertNomeMap.eval :=
  tauLambertValue_continuous

/-- Actual value prefixes converge with the proved Lambert tail. -/
theorem tauLambertNomeMap_close_prefix (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) :
    Small (sub (tauLambertNomeMap.eval q hq).val ((tauLambertPrefixMap 1 N).eval q hq).val)
      (tauLambertTail N) :=
  weightedLambertSum_close q (1/1024) 1 (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ q hq) (by decide +kernel) N

end ComputableAnalysis.ModularForms
