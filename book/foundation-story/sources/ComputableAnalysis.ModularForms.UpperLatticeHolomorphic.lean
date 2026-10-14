import ComputableAnalysis.ModularForms.UpperSquareRemainderBounds
import ComputableAnalysis.ModularForms.UpperLatticeRemainderComparison

/-! Holomorphicity of the actual constructed infinite lattice sums. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem upperWeightFourLatticeMap_remainder_quadratic
    (a : Scalar) (ha : InUpperHalfPlane a.val) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (sub z.val a.val) (upperRadius a ha).val)
    (H : QPos) (hza : Small (sub z.val a.val) H.val) :
    Small (DomainFunctions.remainder upperWeightFourLatticeMap a ha
      ⟨_,derivativeWeightFourSum_valid a ha⟩ z hz) (localWeightFourRemainderConstant a ha*H.val*H.val) := by
  have hd := SeriesLimitLaws.shrinks_scale _ (localDerivativeWeightFourTailRate_shrinks a ha)
    (2*H.val) (Rat.mul_nonneg (by decide) (Rat.le_of_lt H.property))
  have he : (fun n => (2*H.val)*localDerivativeWeightFourTailRate a ha n)=
      (fun n => 2*localDerivativeWeightFourTailRate a ha n*H.val) := by funext n; grind
  rw [he] at hd
  have hv := RepresentedCauchySum.sum_shrinks _ _
    (localWeightFourTailRate_shrinks a ha) (localWeightFourTailRate_shrinks a ha)
  have herror := RepresentedCauchySum.sum_shrinks _ _ hv hd
  exact SeriesLimitLaws.small_of_prefix_bound _ (DomainFunctions.remainder_valid _ _ _ _ _ _)
    (fun n => DomainFunctions.remainder (upperFiniteMap 4 (QuadraticOrder163.squarePoints (n+1))) a ha
      ((upperFiniteMap_holomorphic 4 (QuadraticOrder163.squarePoints (n+1))).derivative a ha) z hz)
    (fun n => DomainFunctions.remainder_valid _ _ _ _ _ _) _ _ herror
    (upperWeightFourLatticeMap_remainder_close_finite a ha z hz hs H hza)
    (fun n => upperFiniteSquare_weightFour_remainder_local_bound a ha z hz hs H.val
      (Rat.le_of_lt H.property) hza (n+1))

def upperWeightFourLatticeMap_hasDerivativeAt (a : Scalar) (ha : InUpperHalfPlane a.val) :
    HasDerivativeAt upperWeightFourLatticeMap a ha ⟨_,derivativeWeightFourSum_valid a ha⟩ where
  delta eps := minRadius (upperRadius a ha)
    (divideRadius eps ⟨localWeightFourRemainderConstant a ha+1, by
      have h := localWeightFourRemainderConstant_nonnegative a ha; grind⟩)
  estimate eps H z hz hH hza := by
    have hs := hza.mono (Rat.le_trans hH (minRadius_left _ _))
    have hb := upperWeightFourLatticeMap_remainder_quadratic a ha z hz hs H hza
    apply hb.mono
    have hC := localWeightFourRemainderConstant_nonnegative a ha
    have hrad := Rat.le_trans hH (minRadius_right _ _)
    have hm := Rat.mul_le_mul_of_nonneg_left hrad (show 0≤localWeightFourRemainderConstant a ha+1 by grind)
    have he := divideRadius_identity eps
      (⟨localWeightFourRemainderConstant a ha+1, by grind⟩ : QPos)
    rw [he] at hm
    have hp := H.property
    have h1 : localWeightFourRemainderConstant a ha*H.val≤eps.val := by grind
    exact Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hp)

def upperWeightFourLatticeMap_holomorphic : Holomorphic upperWeightFourLatticeMap where
  openDomain := ⟨upperRadius,upperRadius_inside⟩
  derivative a ha := ⟨derivativeWeightFourSum a ha,derivativeWeightFourSum_valid a ha⟩
  atPoint := upperWeightFourLatticeMap_hasDerivativeAt
  derivative_congr a b ha hb he := derivativeWeightFourSum_congr a b ha hb he
  continuousDerivative := derivativeWeightFourMap_continuous

theorem upperWeightSixLatticeMap_remainder_quadratic
    (a : Scalar) (ha : InUpperHalfPlane a.val) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (sub z.val a.val) (upperRadius a ha).val)
    (H : QPos) (hza : Small (sub z.val a.val) H.val) :
    Small (DomainFunctions.remainder upperWeightSixLatticeMap a ha
      ⟨_,derivativeWeightSixSum_valid a ha⟩ z hz) (localWeightSixRemainderConstant a ha*H.val*H.val) := by
  have hd := SeriesLimitLaws.shrinks_scale _ (localDerivativeWeightSixTailRate_shrinks a ha)
    (2*H.val) (Rat.mul_nonneg (by decide) (Rat.le_of_lt H.property))
  have he : (fun n => (2*H.val)*localDerivativeWeightSixTailRate a ha n)=
      (fun n => 2*localDerivativeWeightSixTailRate a ha n*H.val) := by funext n; grind
  rw [he] at hd
  have hv := RepresentedCauchySum.sum_shrinks _ _
    (localWeightSixTailRate_shrinks a ha) (localWeightSixTailRate_shrinks a ha)
  have herror := RepresentedCauchySum.sum_shrinks _ _ hv hd
  exact SeriesLimitLaws.small_of_prefix_bound _ (DomainFunctions.remainder_valid _ _ _ _ _ _)
    (fun n => DomainFunctions.remainder (upperFiniteMap 6 (QuadraticOrder163.squarePoints (n+1))) a ha
      ((upperFiniteMap_holomorphic 6 (QuadraticOrder163.squarePoints (n+1))).derivative a ha) z hz)
    (fun n => DomainFunctions.remainder_valid _ _ _ _ _ _) _ _ herror
    (upperWeightSixLatticeMap_remainder_close_finite a ha z hz hs H hza)
    (fun n => upperFiniteSquare_weightSix_remainder_local_bound a ha z hz hs H.val
      (Rat.le_of_lt H.property) hza (n+1))

def upperWeightSixLatticeMap_hasDerivativeAt (a : Scalar) (ha : InUpperHalfPlane a.val) :
    HasDerivativeAt upperWeightSixLatticeMap a ha ⟨_,derivativeWeightSixSum_valid a ha⟩ where
  delta eps := minRadius (upperRadius a ha)
    (divideRadius eps ⟨localWeightSixRemainderConstant a ha+1, by
      have h := localWeightSixRemainderConstant_nonnegative a ha; grind⟩)
  estimate eps H z hz hH hza := by
    have hs := hza.mono (Rat.le_trans hH (minRadius_left _ _))
    have hb := upperWeightSixLatticeMap_remainder_quadratic a ha z hz hs H hza
    apply hb.mono
    have hC := localWeightSixRemainderConstant_nonnegative a ha
    have hrad := Rat.le_trans hH (minRadius_right _ _)
    have hm := Rat.mul_le_mul_of_nonneg_left hrad (show 0≤localWeightSixRemainderConstant a ha+1 by grind)
    have he := divideRadius_identity eps
      (⟨localWeightSixRemainderConstant a ha+1, by grind⟩ : QPos)
    rw [he] at hm
    have hp := H.property
    have h1 : localWeightSixRemainderConstant a ha*H.val≤eps.val := by grind
    exact Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hp)

def upperWeightSixLatticeMap_holomorphic : Holomorphic upperWeightSixLatticeMap where
  openDomain := ⟨upperRadius,upperRadius_inside⟩
  derivative a ha := ⟨derivativeWeightSixSum a ha,derivativeWeightSixSum_valid a ha⟩
  atPoint := upperWeightSixLatticeMap_hasDerivativeAt
  derivative_congr a b ha hb he := derivativeWeightSixSum_congr a b ha hb he
  continuousDerivative := derivativeWeightSixMap_continuous

end ComputableAnalysis.ModularForms
