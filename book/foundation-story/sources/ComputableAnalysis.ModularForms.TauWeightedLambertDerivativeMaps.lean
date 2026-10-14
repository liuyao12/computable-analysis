import ComputableAnalysis.ModularForms.TauWeightedLambertPrefixDerivative
import ComputableAnalysis.RiemannHilbert.DomainUniformLimitContinuity

/-! Continuous maps of the constructed higher weighted Lambert slope sums. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- The represented sum of actual term slopes, on the working nome disk. -/
def tauWeightedLambertSlopeMap (k : Nat) (hk : k≤5) : DomainFunctions.Map where
  domain := tauEulerNomeDomain
  eval := fun q hq => tauWeightedLambertSlopeValue q hq k hk
  domain_congr := tauEulerNomeDomain_openData.invariant
  eval_congr := fun q w hq hw he => tauWeightedLambertSlopeValue_congr q w k hk hq hw he

/-- Actual prefix derivative convergence proves continuity of each higher slope sum. -/
noncomputable def tauWeightedLambertSlopeMap_continuous (k : Nat) (hk : k≤5) :
    ContinuousOn (tauWeightedLambertSlopeMap k hk).domain (tauWeightedLambertSlopeMap k hk).eval :=
  continuousOn_of_uniform_prefixes (fun q hq => tauWeightedLambertSlopeValue q hq k hk)
    (fun N q hq => (tauLambertPrefixMap_holomorphic k N).derivative q hq)
    (fun N => (tauLambertPrefixMap_holomorphic k N).continuousDerivative)
    (fun N => 128*(weightedSlopeRatio k)^N) (tauWeightedLambertSlopeSeries_tail_shrinks k hk)
    (fun N q hq => tauWeightedLambertSlopeValue_close_actual_derivative q hq k hk N)

end ComputableAnalysis.ModularForms
