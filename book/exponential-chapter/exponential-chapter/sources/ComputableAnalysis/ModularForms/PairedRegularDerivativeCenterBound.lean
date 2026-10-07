import ComputableAnalysis.ModularForms.PairedLaurentCubicApproximation

/-! Quantitative derivative normalization from actual derivative estimates. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedRegularPartDerivative_center_bound (z : Scalar) (hz : LocalODE.interior (1/4) z)
    (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (sub (pairedRegularPartDerivative z hz).val pairedZeroSquareSum) (13824*R*R) := by
  have hzero := equiv_refl _ pairedZeroScalar.property
  have hT := pairedRegularDivision_center_difference_bound pairedZeroScalar z pairedZeroScalar_interior hz hzero R hR hs
  have hc := pairedRegularDivisionValue_at_zero pairedZeroScalar pairedZeroScalar_interior hzero
  have hTc := Small.congr
    (sub_valid (pairedRegularDivisionMap.eval z hz).property
      (pairedRegularDivisionMap.eval pairedZeroScalar pairedZeroScalar_interior).property)
    (sub_valid (pairedRegularDivisionMap.eval z hz).property pairedZeroSquareSum_valid)
    (FunctionTheory.sub_congr (equiv_refl _ (pairedRegularDivisionMap.eval z hz).property) hc) hT
  have hx : (sub z.val pairedZeroScalar.val).Equiv z.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid z.property pairedZeroScalar.property) (hright := z.property)
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change Z-0=Z
    grind only
  have hd := Small.congr z.property (sub_valid z.property pairedZeroScalar.property) (equiv_symm hx) hs
  have hD := pairedRegularDivisionDerivativeValue_difference_bound pairedZeroScalar z pairedZeroScalar_interior hz R hR hd
  have hd0 := pairedRegularDivisionDerivative_at_zero pairedZeroScalar pairedZeroScalar_interior hzero
  have hDz : (sub (pairedRegularDivisionDerivative z hz).val
      (pairedRegularDivisionDerivative pairedZeroScalar pairedZeroScalar_interior).val).Equiv
      (pairedRegularDivisionDerivative z hz).val := by
    have hq := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (pairedRegularDivisionDerivative pairedZeroScalar pairedZeroScalar_interior).property)
      (hright := ofQComplex_valid _) hd0
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (pairedRegularDivisionDerivative z hz).property
        (pairedRegularDivisionDerivative pairedZeroScalar pairedZeroScalar_interior).property)
      (hright := (pairedRegularDivisionDerivative z hz).property)
    let D := ComplexRawQuotient.ofRaw (pairedRegularDivisionDerivative z hz).val (pairedRegularDivisionDerivative z hz).property
    let A := ComplexRawQuotient.ofRaw (pairedRegularDivisionDerivative pairedZeroScalar pairedZeroScalar_interior).val
      (pairedRegularDivisionDerivative pairedZeroScalar pairedZeroScalar_interior).property
    change A=0 at hq
    change D-A=D
    grind only
  have hDb := Small.congr
    (sub_valid (pairedRegularDivisionDerivative z hz).property (pairedRegularDivisionDerivative pairedZeroScalar pairedZeroScalar_interior).property)
    (pairedRegularDivisionDerivative z hz).property hDz hD
  have hm := Small.mul z.property (pairedRegularDivisionDerivative z hz).property hR
    (Rat.mul_nonneg (show (0:Rat)≤4608 by decide) hR) hs hDb
  have hb := LocalODE.small_add hTc hm
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedRegularPartDerivative z hz).property)
    (hright := add_valid (pairedRegularDivisionMap.eval z hz).property (mul_valid z.property (pairedRegularDivisionDerivative z hz).property))
    (pairedRegularPartDerivative_division z hz)
  have he : (add (sub (pairedRegularDivisionMap.eval z hz).val pairedZeroSquareSum)
      (mul z.val (pairedRegularDivisionDerivative z hz).val)).Equiv
      (sub (pairedRegularPartDerivative z hz).val pairedZeroSquareSum) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid (pairedRegularDivisionMap.eval z hz).property pairedZeroSquareSum_valid)
        (mul_valid z.property (pairedRegularDivisionDerivative z hz).property))
      (hright := sub_valid (pairedRegularPartDerivative z hz).property pairedZeroSquareSum_valid)
    let S := ComplexRawQuotient.ofRaw (pairedRegularPartDerivative z hz).val (pairedRegularPartDerivative z hz).property
    let T := ComplexRawQuotient.ofRaw (pairedRegularDivisionMap.eval z hz).val (pairedRegularDivisionMap.eval z hz).property
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    let D := ComplexRawQuotient.ofRaw (pairedRegularDivisionDerivative z hz).val (pairedRegularDivisionDerivative z hz).property
    let C := ComplexRawQuotient.ofRaw pairedZeroSquareSum pairedZeroSquareSum_valid
    change S=T+Z*D at hp
    change (T-C)+Z*D=S-C
    grind only
  exact (Small.congr
    (add_valid (sub_valid (pairedRegularDivisionMap.eval z hz).property pairedZeroSquareSum_valid)
      (mul_valid z.property (pairedRegularDivisionDerivative z hz).property))
    (sub_valid (pairedRegularPartDerivative z hz).property pairedZeroSquareSum_valid) he hb).mono (by grind only)

end ComputableAnalysis.ModularForms
