import ComputableAnalysis.ModularForms.PairedRegularDivisionQuadraticCenter

/-! Cubic local normalization with an actual inverse-square coefficient. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedRegularPart_cubic_center_bound (z : Scalar) (hz : LocalODE.interior (1/4) z)
    (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (sub (pairedRegularPartMap.eval z hz).val (mul z.val pairedZeroSquareSum)) (9216*R*R*R) := by
  have hb := pairedRegularDivision_center_difference_bound pairedZeroScalar z pairedZeroScalar_interior hz
    (equiv_refl _ pairedZeroScalar.property) R hR hs
  have hc := pairedRegularDivisionValue_at_zero pairedZeroScalar pairedZeroScalar_interior
    (equiv_refl _ pairedZeroScalar.property)
  have hbc := Small.congr
    (sub_valid (pairedRegularDivisionMap.eval z hz).property
      (pairedRegularDivisionMap.eval pairedZeroScalar pairedZeroScalar_interior).property)
    (sub_valid (pairedRegularDivisionMap.eval z hz).property pairedZeroSquareSum_valid)
    (FunctionTheory.sub_congr (equiv_refl _ (pairedRegularDivisionMap.eval z hz).property) hc) hb
  have hm := Small.mul z.property
    (sub_valid (pairedRegularDivisionMap.eval z hz).property pairedZeroSquareSum_valid)
    hR (Rat.mul_nonneg (Rat.mul_nonneg (show (0:Rat)≤4608 by decide) hR) hR) hs hbc
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property (pairedRegularDivisionMap.eval z hz).property)
    (hright := (pairedRegularPartMap.eval z hz).property)
    (pairedRegularDivisionValue_product z (LocalODE.interior_bound _ z hz))
  have he : (mul z.val (sub (pairedRegularDivisionMap.eval z hz).val pairedZeroSquareSum)).Equiv
      (sub (pairedRegularPartMap.eval z hz).val (mul z.val pairedZeroSquareSum)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid z.property (sub_valid (pairedRegularDivisionMap.eval z hz).property pairedZeroSquareSum_valid))
      (hright := sub_valid (pairedRegularPartMap.eval z hz).property (mul_valid z.property pairedZeroSquareSum_valid))
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    let T := ComplexRawQuotient.ofRaw (pairedRegularDivisionMap.eval z hz).val (pairedRegularDivisionMap.eval z hz).property
    let S := ComplexRawQuotient.ofRaw (pairedRegularPartMap.eval z hz).val (pairedRegularPartMap.eval z hz).property
    let C := ComplexRawQuotient.ofRaw pairedZeroSquareSum pairedZeroSquareSum_valid
    change Z*T=S at hp
    change Z*(T-C)=S-Z*C
    grind only
  exact (Small.congr
    (mul_valid z.property (sub_valid (pairedRegularDivisionMap.eval z hz).property pairedZeroSquareSum_valid))
    (sub_valid (pairedRegularPartMap.eval z hz).property (mul_valid z.property pairedZeroSquareSum_valid)) he hm).mono
    (by grind only)

end ComputableAnalysis.ModularForms
