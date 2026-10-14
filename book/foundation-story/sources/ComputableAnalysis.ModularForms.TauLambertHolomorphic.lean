import ComputableAnalysis.ModularForms.TauLambertUniformRemainder
import ComputableAnalysis.ModularForms.TauLambertRemainderLimit

/-! Actual holomorphicity of the convergent degree-one Lambert value. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem tauLambertValue_remainder_bound (a z : Scalar) (ha : tauEulerNomeDomain a)
    (hz : tauEulerNomeDomain z) (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (SeriesLimitLaws.remainder (tauLambertValue z hz).val (tauLambertValue a ha).val
      (tauLambertSlopeValue a ha).val (sub z.val a.val)) (71680*H^2) := by
  apply SeriesLimitLaws.small_of_prefix_bound _
    (SeriesLimitLaws.remainder_valid _ _ _ _ (tauLambertValue z hz).property
      (tauLambertValue a ha).property (tauLambertSlopeValue a ha).property (sub_valid z.property a.property))
    (fun N => SeriesLimitLaws.remainder ((tauLambertPrefixMap 1 N).eval z hz).val
      ((tauLambertPrefixMap 1 N).eval a ha).val
      ((tauLambertPrefixMap_holomorphic 1 N).derivative a ha).val (sub z.val a.val))
    (fun N => SeriesLimitLaws.remainder_valid _ _ _ _ ((tauLambertPrefixMap 1 N).eval z hz).property
      ((tauLambertPrefixMap 1 N).eval a ha).property
      ((tauLambertPrefixMap_holomorphic 1 N).derivative a ha).property (sub_valid z.property a.property))
    (71680*H^2) _ (tauLambertRemainder_prefix_error_shrinks H hH)
    (fun N => tauLambertRemainder_close_prefix a z ha hz H hH hd N)
    (fun N => tauLambertPrefix_uniform_remainder_bound a z ha hz H hH hd N)

def tauLambertNomeMap_hasDerivativeAt (a : Scalar) (ha : tauEulerNomeDomain a) :
    HasDerivativeAt tauLambertNomeMap a ha (tauLambertSlopeValue a ha) where
  delta eps := divideRadius eps ⟨71680,by decide +kernel⟩
  estimate eps H z hz hH hd := by
    have hb := tauLambertValue_remainder_bound a z ha hz H.val (Rat.le_of_lt H.property) hd
    have hm := Rat.mul_le_mul_of_nonneg_left hH (by decide +kernel : (0:Rat)≤71680)
    rw [divideRadius_identity eps ⟨71680,by decide +kernel⟩] at hm
    have hp := Rat.mul_le_mul_of_nonneg_right hm (Rat.le_of_lt H.property)
    apply hb.mono
    rw [Rat.pow_succ, Rat.pow_one]
    grind only

noncomputable def tauLambertNomeMap_holomorphic : Holomorphic tauLambertNomeMap where
  openDomain := ⟨tauEulerNomeDomain_openData.radius,tauEulerNomeDomain_openData.inside⟩
  derivative := tauLambertSlopeValue
  atPoint := tauLambertNomeMap_hasDerivativeAt
  derivative_congr := tauLambertSlopeValue_congr
  continuousDerivative := tauLambertSlopeMap_continuous

end ComputableAnalysis.ModularForms
