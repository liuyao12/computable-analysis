import ComputableAnalysis.ModularForms.PairedLaurentDerivativeAgreement

/-! Actual double-pole cancellation in the lattice Riccati expression. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedRiccatiRegularExpression (z : Scalar) (hz : LocalODE.interior (1/4) z) : Scalar :=
  let zz := DomainFunctions.scalarProduct z z
  let s := pairedRegularPartMap.eval z hz
  let d := pairedRegularPartDerivative z hz
  let zs := DomainFunctions.scalarProduct z s
  DomainFunctions.scalarSum (DomainFunctions.scalarProduct zz d)
    (DomainFunctions.scalarSum (DomainFunctions.scalarSum zs zs)
      (DomainFunctions.scalarProduct zz (DomainFunctions.scalarProduct s s)))

theorem pairedLaurent_riccati_pole_cancellation (z : Scalar) (hz : pairedZeroLaurentMap.domain z) :
    (mul (mul z.val z.val) (add (pairedZeroLaurentMap_holomorphic.derivative z hz).val
      (mul (pairedZeroLaurentMap.eval z hz).val (pairedZeroLaurentMap.eval z hz).val))).Equiv
      (pairedRiccatiRegularExpression z hz.1).val := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property (RepresentedReciprocal.inverse z hz.2).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse z hz.2)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (mul_valid z.property z.property)
      (add_valid (pairedZeroLaurentMap_holomorphic.derivative z hz).property
        (mul_valid (pairedZeroLaurentMap.eval z hz).property (pairedZeroLaurentMap.eval z hz).property)))
    (hright := (pairedRiccatiRegularExpression z hz.1).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse z hz.2).val (RepresentedReciprocal.inverse z hz.2).property
  let S := ComplexRawQuotient.ofRaw (pairedRegularPartMap.eval z hz.1).val (pairedRegularPartMap.eval z hz.1).property
  let D := ComplexRawQuotient.ofRaw (pairedRegularPartDerivative z hz.1).val (pairedRegularPartDerivative z hz.1).property
  change Z*I=1 at hi
  change (Z*Z)*((-(I*I)+D)+(I+S)*(I+S))=(Z*Z)*D+((Z*S+Z*S)+(Z*Z)*(S*S))
  grind only

theorem pairedRiccatiRegularExpression_zero (z : Scalar) (hz : LocalODE.interior (1/4) z)
    (he : z.val.Equiv zero) : (pairedRiccatiRegularExpression z hz).val.Equiv zero := by
  have hzero := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := z.property) (hright := ofQComplex_valid _) he
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedRiccatiRegularExpression z hz).property) (hright := ofQComplex_valid _)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let S := ComplexRawQuotient.ofRaw (pairedRegularPartMap.eval z hz).val (pairedRegularPartMap.eval z hz).property
  let D := ComplexRawQuotient.ofRaw (pairedRegularPartDerivative z hz).val (pairedRegularPartDerivative z hz).property
  change Z=0 at hzero
  change (Z*Z)*D+((Z*S+Z*S)+(Z*Z)*(S*S))=0
  grind only

end ComputableAnalysis.ModularForms
