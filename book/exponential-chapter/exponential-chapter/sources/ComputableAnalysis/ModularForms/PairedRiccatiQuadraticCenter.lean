import ComputableAnalysis.ModularForms.PairedRegularDerivativeCenterBound

/-! Quantitative center normalization of the actual Riccati extension. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedRiccatiCenterConstant : Scalar :=
  ⟨add pairedZeroSquareSum (add pairedZeroSquareSum pairedZeroSquareSum),
    add_valid pairedZeroSquareSum_valid (add_valid pairedZeroSquareSum_valid pairedZeroSquareSum_valid)⟩

theorem pairedRiccatiExtension_center_bound (z : Scalar) (hz : LocalODE.interior (1/4) z)
    (R : Rat) (hR : 0≤R) (hRq : R≤(1:Rat)/4) (hs : Small z.val R) :
    Small (sub (pairedRiccatiExtension z hz).val pairedRiccatiCenterConstant.val) (25088*R*R) := by
  have hD := pairedRegularPartDerivative_center_bound z hz R hR hs
  have hT := pairedRegularDivision_center_difference_bound pairedZeroScalar z pairedZeroScalar_interior hz
    (equiv_refl _ pairedZeroScalar.property) R hR hs
  have hc := pairedRegularDivisionValue_at_zero pairedZeroScalar pairedZeroScalar_interior
    (equiv_refl _ pairedZeroScalar.property)
  have ht := Small.congr
    (sub_valid (pairedRegularDivisionMap.eval z hz).property
      (pairedRegularDivisionMap.eval pairedZeroScalar pairedZeroScalar_interior).property)
    (sub_valid (pairedRegularDivisionMap.eval z hz).property pairedZeroSquareSum_valid)
    (FunctionTheory.sub_congr (equiv_refl _ (pairedRegularDivisionMap.eval z hz).property) hc) hT
  have hS := pairedRegularPart_bound z (LocalODE.interior_bound _ z hz) R hR hRq hs
  have hss := Small.mul (pairedRegularPartMap.eval z hz).property (pairedRegularPartMap.eval z hz).property
    (Rat.mul_nonneg (show (0:Rat)≤32 by decide) hR) (Rat.mul_nonneg (show (0:Rat)≤32 by decide) hR) hS hS
  have hb := LocalODE.small_add hD (LocalODE.small_add (LocalODE.small_add ht ht) hss)
  have he : (add (sub (pairedRegularPartDerivative z hz).val pairedZeroSquareSum)
      (add (add (sub (pairedRegularDivisionMap.eval z hz).val pairedZeroSquareSum)
        (sub (pairedRegularDivisionMap.eval z hz).val pairedZeroSquareSum))
        (mul (pairedRegularPartMap.eval z hz).val (pairedRegularPartMap.eval z hz).val))).Equiv
      (sub (pairedRiccatiExtension z hz).val pairedRiccatiCenterConstant.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid (pairedRegularPartDerivative z hz).property pairedZeroSquareSum_valid)
        (add_valid (add_valid (sub_valid (pairedRegularDivisionMap.eval z hz).property pairedZeroSquareSum_valid)
          (sub_valid (pairedRegularDivisionMap.eval z hz).property pairedZeroSquareSum_valid))
          (mul_valid (pairedRegularPartMap.eval z hz).property (pairedRegularPartMap.eval z hz).property)))
      (hright := sub_valid (pairedRiccatiExtension z hz).property pairedRiccatiCenterConstant.property)
    let D := ComplexRawQuotient.ofRaw (pairedRegularPartDerivative z hz).val (pairedRegularPartDerivative z hz).property
    let T := ComplexRawQuotient.ofRaw (pairedRegularDivisionMap.eval z hz).val (pairedRegularDivisionMap.eval z hz).property
    let S := ComplexRawQuotient.ofRaw (pairedRegularPartMap.eval z hz).val (pairedRegularPartMap.eval z hz).property
    let C := ComplexRawQuotient.ofRaw pairedZeroSquareSum pairedZeroSquareSum_valid
    change (D-C)+(((T-C)+(T-C))+S*S)=(D+((T+T)+S*S))-(C+(C+C))
    grind only
  exact (Small.congr
    (add_valid (sub_valid (pairedRegularPartDerivative z hz).property pairedZeroSquareSum_valid)
      (add_valid (add_valid (sub_valid (pairedRegularDivisionMap.eval z hz).property pairedZeroSquareSum_valid)
        (sub_valid (pairedRegularDivisionMap.eval z hz).property pairedZeroSquareSum_valid))
        (mul_valid (pairedRegularPartMap.eval z hz).property (pairedRegularPartMap.eval z hz).property)))
    (sub_valid (pairedRiccatiExtension z hz).property pairedRiccatiCenterConstant.property) he hb).mono (by grind only)

end ComputableAnalysis.ModularForms
