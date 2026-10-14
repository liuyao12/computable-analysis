import ComputableAnalysis.ModularForms.WideLambertThirdValueRemainder
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Actual executable larger-disk evaluator with represented-value invariance. -/
def wideLambertThirdMap : DomainFunctions.Map where
  domain := wideLambertFifthDomain
  eval q hq := wideLambertThirdValue q (LocalODE.interior_bound _ q hq)
  domain_congr := wideLambertFifthDomain_openData.invariant
  eval_congr q w hq hw he := wideLambertThirdValue_congr q w
    (LocalODE.interior_bound _ q hq) (LocalODE.interior_bound _ w hw) he

/-- The wider slope sum is the actual derivative at every represented point of the open disk. -/
def wideLambertThirdMap_hasDerivativeAt (a : Scalar) (ha : wideLambertFifthDomain a) :
    HasDerivativeAt wideLambertThirdMap a ha
      (wideLambertThirdSlopeValue a (LocalODE.interior_bound _ a ha)) where
  delta eps := divideRadius eps (⟨135168,by decide +kernel⟩ : QPos)
  estimate eps H z hz hH hd := by
    have hb := wideLambertThirdValue_remainder_bound a z (LocalODE.interior_bound _ a ha)
      (LocalODE.interior_bound _ z hz) H.val (Rat.le_of_lt H.property) hd
    have hm := Rat.mul_le_mul_of_nonneg_left hH (show (0:Rat)≤135168 by decide +kernel)
    rw [divideRadius_identity eps (⟨135168,by decide +kernel⟩ : QPos)] at hm
    have hh := Rat.mul_le_mul_of_nonneg_right hm (Rat.le_of_lt H.property)
    apply hb.mono
    change 135168*H.val≤eps.val at hm
    rw [Rat.pow_succ H.val 1,Rat.pow_one]
    grind only

/-- Exact evaluator agreement on the original chart, with wider domain evidence constructed. -/
theorem wideLambertThirdMap_tau_agreement (q : Scalar) (hq : tauEulerNomeDomain q) :
    (wideLambertThirdMap.eval q (tauEulerNomeDomain_wide_fifth_mem q hq)).val.Equiv
      (tauHigherLambertValue q hq 3 (by decide +kernel)).val :=
  wideLambertThirdValue_tau_agreement q hq _
end ComputableAnalysis.ModularForms
