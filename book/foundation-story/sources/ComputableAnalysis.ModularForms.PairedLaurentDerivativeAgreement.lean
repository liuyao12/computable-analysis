import ComputableAnalysis.ModularForms.PairedDerivativePoleNormalization

/-! Laurent derivative agreement with the canonical upper-half-plane derivative. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedLaurentUpperDomain (z : Scalar) : Prop :=
  InUpperHalfPlane z.val ∧ pairedZeroLaurentMap.domain z

def pairedLaurentUpperOpenData : ScalarTopology.OpenData pairedLaurentUpperDomain where
  invariant z w he := and_congr (pairedPartialFractionMap.domain_congr z w he)
    (pairedZeroLaurentMap.domain_congr z w he)
  radius z hz := minRadius (pairedPartialFractionMap_holomorphic.openDomain.radius z hz.1)
    (pairedZeroLaurentMap_holomorphic.openDomain.radius z hz.2)
  inside a ha z hd :=
    ⟨pairedPartialFractionMap_holomorphic.openDomain.inside a ha.1 z (hd.mono (minRadius_left _ _)),
      pairedZeroLaurentMap_holomorphic.openDomain.inside a ha.2 z (hd.mono (minRadius_right _ _))⟩

theorem pairedLaurentDerivative_upper_agreement (z : Scalar) (hz : pairedZeroLaurentMap.domain z)
    (hu : InUpperHalfPlane z.val) :
    (pairedZeroLaurentMap_holomorphic.derivative z hz).val.Equiv (pairedPartialFractionDerivative z hu).val := by
  let f := onDomain pairedPartialFractionMap pairedLaurentUpperOpenData.invariant
    (fun (w : Scalar) (hw : pairedLaurentUpperDomain w) => hw.1)
  let hf := pairedPartialFractionMap_holomorphic.onDomain pairedLaurentUpperOpenData
    (fun (w : Scalar) (hw : pairedLaurentUpperDomain w) => hw.1)
  let hg : Holomorphic f := pairedZeroLaurentMap_holomorphic.transfer f
    (fun (w : Scalar) (hw : pairedLaurentUpperDomain w) => hw.2)
    ⟨pairedLaurentUpperOpenData.radius,pairedLaurentUpperOpenData.inside⟩
    (fun w hw => pairedZeroLaurentMap_upper w hw.2 hw.1)
  exact hg.derivative_unique hf z ⟨hu,hz⟩

theorem pairedPartialFractionDerivative_local_normalization (z : Scalar)
    (hz : pairedZeroLaurentMap.domain z) (hu : InUpperHalfPlane z.val) :
    (add (mul (mul z.val z.val) (pairedPartialFractionDerivative z hu).val)
      (ofQComplex QComplex.one)).Equiv
      (mul (mul z.val z.val) (pairedRegularPartDerivative z hz.1).val) := by
  have he := add_equiv
    (mul_equiv (mul_valid z.property z.property) (mul_valid z.property z.property)
      (pairedPartialFractionDerivative z hu).property (pairedZeroLaurentMap_holomorphic.derivative z hz).property
      (equiv_refl _ (mul_valid z.property z.property)) (equiv_symm (pairedLaurentDerivative_upper_agreement z hz hu)))
    (equiv_refl (ofQComplex QComplex.one) (ofQComplex_valid _))
  exact equiv_trans
    (add_valid (mul_valid (mul_valid z.property z.property) (pairedPartialFractionDerivative z hu).property) (ofQComplex_valid _))
    (add_valid (mul_valid (mul_valid z.property z.property) (pairedZeroLaurentMap_holomorphic.derivative z hz).property) (ofQComplex_valid _))
    (mul_valid (mul_valid z.property z.property) (pairedRegularPartDerivative z hz.1).property)
    he (pairedLaurentDerivative_normalization z hz)

theorem pairedPartialFractionDerivative_local_bound (z : Scalar)
    (hz : pairedZeroLaurentMap.domain z) (hu : InUpperHalfPlane z.val)
    (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (add (mul (mul z.val z.val) (pairedPartialFractionDerivative z hu).val)
      (ofQComplex QComplex.one)) (8192*R*R) := by
  have he := add_equiv
    (mul_equiv (mul_valid z.property z.property) (mul_valid z.property z.property)
      (pairedZeroLaurentMap_holomorphic.derivative z hz).property (pairedPartialFractionDerivative z hu).property
      (equiv_refl _ (mul_valid z.property z.property)) (pairedLaurentDerivative_upper_agreement z hz hu))
    (equiv_refl (ofQComplex QComplex.one) (ofQComplex_valid _))
  exact Small.congr
    (add_valid (mul_valid (mul_valid z.property z.property) (pairedZeroLaurentMap_holomorphic.derivative z hz).property) (ofQComplex_valid _))
    (add_valid (mul_valid (mul_valid z.property z.property) (pairedPartialFractionDerivative z hu).property) (ofQComplex_valid _))
    he (pairedLaurentDerivative_normalization_bound z hz R hR hs)

end ComputableAnalysis.ModularForms
