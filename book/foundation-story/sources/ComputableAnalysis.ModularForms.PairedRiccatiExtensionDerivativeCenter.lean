import ComputableAnalysis.ModularForms.PairedIntegerRiccatiExtension

/-! The actual Riccati extension has zero analytic derivative at its center. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedRiccatiExtension_hasDerivativeAt_zero (a : Scalar)
    (ha : pairedRiccatiExtensionMap.domain a) (he : a.val.Equiv zero) :
    HasDerivativeAt pairedRiccatiExtensionMap a ha ⟨zero,ofQComplex_valid _⟩ where
  delta eps := minRadius ⟨1/4,by decide +kernel⟩
    (divideRadius eps ⟨25088,by decide +kernel⟩)
  estimate eps H z hz hH hd := by
    have haz := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := a.property) (hright := ofQComplex_valid _) he
    have hdiff : (sub z.val a.val).Equiv z.val := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := sub_valid z.property a.property) (hright := z.property)
      let Z := ComplexRawQuotient.ofRaw z.val z.property
      let A := ComplexRawQuotient.ofRaw a.val a.property
      change A=0 at haz
      change Z-A=Z
      grind only
    have hs := Small.congr (sub_valid z.property a.property) z.property hdiff hd
    have hb := pairedRiccatiExtension_center_bound z hz H.val (Rat.le_of_lt H.property)
      (Rat.le_trans hH (minRadius_left _ _)) hs
    have hc := pairedRiccatiExtension_center_identity a ha he
    have hr : (sub (pairedRiccatiExtension z hz).val pairedRiccatiCenterConstant.val).Equiv
        (DomainFunctions.remainder pairedRiccatiExtensionMap a ha ⟨zero,ofQComplex_valid _⟩ z hz) := by
      have hce := ComplexRawQuotient.ofRaw_eq_ofRaw
        (hleft := (pairedRiccatiExtension a ha).property)
        (hright := pairedRiccatiCenterConstant.property) hc
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := sub_valid (pairedRiccatiExtension z hz).property pairedRiccatiCenterConstant.property)
        (hright := DomainFunctions.remainder_valid _ _ _ _ _ _)
      let E := ComplexRawQuotient.ofRaw (pairedRiccatiExtension z hz).val (pairedRiccatiExtension z hz).property
      let C := ComplexRawQuotient.ofRaw pairedRiccatiCenterConstant.val pairedRiccatiCenterConstant.property
      let EA := ComplexRawQuotient.ofRaw (pairedRiccatiExtension a ha).val (pairedRiccatiExtension a ha).property
      let Z := ComplexRawQuotient.ofRaw z.val z.property
      let A := ComplexRawQuotient.ofRaw a.val a.property
      change EA=C at hce
      change E-C=(E-EA)-0*(Z-A)
      grind only
    apply (Small.congr (sub_valid (pairedRiccatiExtension z hz).property pairedRiccatiCenterConstant.property)
      (DomainFunctions.remainder_valid _ _ _ _ _ _) hr hb).mono
    have hm := Rat.mul_le_mul_of_nonneg_left
      (Rat.le_trans hH (minRadius_right _ _)) (show (0:Rat)≤25088 by decide +kernel)
    rw [divideRadius_identity eps ⟨25088,by decide +kernel⟩] at hm
    exact Rat.mul_le_mul_of_nonneg_right hm (Rat.le_of_lt H.property)

theorem pairedRiccatiExtension_derivative_at_zero (a : Scalar)
    (ha : pairedRiccatiExtensionMap.domain a) (he : a.val.Equiv zero) :
    (pairedRiccatiExtensionMap_holomorphic.derivative a ha).val.Equiv zero :=
  (pairedRiccatiExtensionMap_holomorphic.atPoint a ha).unique
    (pairedRiccatiExtension_hasDerivativeAt_zero a ha he)
    pairedRiccatiExtensionMap_holomorphic.openDomain


theorem pairedIntegerRiccatiExtension_derivative_at_integer (k : Int) (z : Scalar)
    (hz : (pairedIntegerRiccatiExtensionMap k).domain z)
    (he : z.val.Equiv (rationalInteger k).val) :
    ((pairedIntegerRiccatiExtensionMap_holomorphic k).derivative z hz).val.Equiv zero := by
  let w := integerShiftScalar z (-k)
  have hw := compose_outer_mem hz
  have hc := pairedRiccatiExtension_derivative_at_zero w hw
    (integerShiftScalar_at_integer k z he)
  have hd : ((pairedIntegerRiccatiExtensionMap_holomorphic k).derivative z hz).val.Equiv
      (pairedRiccatiExtensionMap_holomorphic.derivative w hw).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((pairedIntegerRiccatiExtensionMap_holomorphic k).derivative z hz).property)
      (hright := (pairedRiccatiExtensionMap_holomorphic.derivative w hw).property)
    let D := ComplexRawQuotient.ofRaw (pairedRiccatiExtensionMap_holomorphic.derivative w hw).val
      (pairedRiccatiExtensionMap_holomorphic.derivative w hw).property
    change D*ComplexRawQuotient.ofQComplex ⟨(1:Rat),0⟩=D
    have ho : ComplexRawQuotient.ofQComplex ⟨(1:Rat),0⟩ = ((1:Int):ComplexRawQuotient.Value) := by
      simpa only [Rat.intCast_one] using integer_constant (1:Int)
    rw [ho]
    grind only
  exact equiv_trans ((pairedIntegerRiccatiExtensionMap_holomorphic k).derivative z hz).property
    (pairedRiccatiExtensionMap_holomorphic.derivative w hw).property (ofQComplex_valid _) hd hc


theorem pairedIntegerRiccatiExtension_center_bound (k : Int) (z : Scalar)
    (hz : (pairedIntegerRiccatiExtensionMap k).domain z)
    (R : Rat) (hR : 0≤R) (hRq : R≤(1:Rat)/4)
    (hs : Small (integerShiftScalar z (-k)).val R) :
    Small (sub ((pairedIntegerRiccatiExtensionMap k).eval z hz).val
      pairedRiccatiCenterConstant.val) (25088*R*R) :=
  pairedRiccatiExtension_center_bound (integerShiftScalar z (-k))
    (compose_outer_mem hz) R hR hRq hs

end ComputableAnalysis.ModularForms
