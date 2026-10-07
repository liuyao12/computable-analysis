import ComputableAnalysis.ModularForms.PairedLaurentDerivative

/-! Exact cancellation and quadratic bounds for the derivative's double pole. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedLaurentDerivative_normalization (z : Scalar) (hz : pairedZeroLaurentMap.domain z) :
    (add (mul (mul z.val z.val) (pairedZeroLaurentMap_holomorphic.derivative z hz).val)
      (ofQComplex QComplex.one)).Equiv
      (mul (mul z.val z.val) (pairedRegularPartDerivative z hz.1).val) := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property (RepresentedReciprocal.inverse z hz.2).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse z hz.2)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := add_valid (mul_valid (mul_valid z.property z.property)
      (pairedZeroLaurentMap_holomorphic.derivative z hz).property) (ofQComplex_valid _))
    (hright := mul_valid (mul_valid z.property z.property) (pairedRegularPartDerivative z hz.1).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse z hz.2).val (RepresentedReciprocal.inverse z hz.2).property
  let D := ComplexRawQuotient.ofRaw (pairedRegularPartDerivative z hz.1).val (pairedRegularPartDerivative z hz.1).property
  change Z*I=1 at hi
  change (Z*Z)*(-(I*I)+D)+1=(Z*Z)*D
  grind only

theorem pairedLaurentDerivative_normalization_bound (z : Scalar) (hz : pairedZeroLaurentMap.domain z)
    (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (add (mul (mul z.val z.val) (pairedZeroLaurentMap_holomorphic.derivative z hz).val)
      (ofQComplex QComplex.one)) (8192*R*R) := by
  have h2 := Small.mul z.property z.property hR hR hs hs
  have h2R : 0≤2*R*R := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hR) hR
  have hd := pairedSmallDiskDerivativeValue_bound z (LocalODE.interior_bound _ z hz.1)
  have hb := (Small.mul (mul_valid z.property z.property) (pairedRegularPartDerivative z hz.1).property
    h2R (show (0:Rat)≤2048 by decide) h2 hd).mono
    (show (2:Rat)*(2*R*R)*2048≤8192*R*R by grind only)
  exact Small.congr (mul_valid (mul_valid z.property z.property) (pairedRegularPartDerivative z hz.1).property)
    (add_valid (mul_valid (mul_valid z.property z.property)
      (pairedZeroLaurentMap_holomorphic.derivative z hz).property) (ofQComplex_valid _))
    (equiv_symm (pairedLaurentDerivative_normalization z hz)) hb

end ComputableAnalysis.ModularForms
