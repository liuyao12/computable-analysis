import ComputableAnalysis.ModularForms.PairedDivisionDerivativeRemainderIdentity
import ComputableAnalysis.ModularForms.PairedRegularDivisionDifferentiable

/-! Actual second differentiability of the division series on its open quarter chart. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedDivisionFirstDerivativeMap : DomainFunctions.Map where
  domain := LocalODE.interior (1/4)
  eval := pairedRegularDivisionDerivative
  domain_congr := pairedRegularDivisionMap.domain_congr
  eval_congr := pairedRegularDivisionDerivative_congr

def pairedDivisionFirstDerivativeMap_hasDerivativeAt (a : Scalar)
    (ha : pairedDivisionFirstDerivativeMap.domain a) :
    HasDerivativeAt pairedDivisionFirstDerivativeMap a ha
      (pairedDivisionSecondDerivativeMap.eval a ha) where
  delta eps := divideRadius eps ⟨122880,by decide +kernel⟩
  estimate eps H z hz hH hd := by
    have h := pairedDivisionDerivative_sum_remainder_bound a z ha hz H.val
      (Rat.le_of_lt H.property) hd
    apply h.mono
    have hm := Rat.mul_le_mul_of_nonneg_left hH (show (0:Rat)≤122880 by decide)
    rw [divideRadius_identity eps ⟨122880,by decide +kernel⟩] at hm
    exact Rat.mul_le_mul_of_nonneg_right hm (Rat.le_of_lt H.property)

end ComputableAnalysis.ModularForms
