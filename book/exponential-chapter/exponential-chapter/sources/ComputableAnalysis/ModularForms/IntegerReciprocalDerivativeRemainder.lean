import ComputableAnalysis.ModularForms.PairedGlobalSecondDerivativeTerms

/-! Exact quadratic remainder decomposition for global squared reciprocals. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def integerReciprocalDerivativeRemainder (k : Int) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) : Scalar :=
  let i := (integerReciprocalMap k).eval a ha
  let j := (integerReciprocalMap k).eval z hz
  let h : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
  let d : Scalar := ⟨sub j.val i.val,sub_valid j.property i.property⟩
  let r := DomainFunctions.scalarProduct
    (DomainFunctions.scalarProduct (DomainFunctions.scalarProduct i i) j)
    (DomainFunctions.scalarProduct h h)
  let ir := DomainFunctions.scalarProduct i r
  scalarNeg (scalarSum (scalarSum ir ir) (DomainFunctions.scalarProduct d d))

theorem integerReciprocalDerivativeMap_remainder (k : Int) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) :
    (DomainFunctions.remainder (integerReciprocalDerivativeMap k) a ha
      (integerReciprocalSecondDerivative k a ha) z hz).Equiv
      (integerReciprocalDerivativeRemainder k a z ha hz).val := by
  let i := (integerReciprocalMap k).eval a ha
  let j := (integerReciprocalMap k).eval z hz
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (integerShiftScalar a k).property i.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (integerShiftScalar a k)
      (upperScalar_nonzero _ (integerShiftScalar_upper a ha k)))
  have hj := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (integerShiftScalar z k).property j.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (integerShiftScalar z k)
      (upperScalar_nonzero _ (integerShiftScalar_upper z hz k)))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := DomainFunctions.remainder_valid _ _ _ _ _ _)
    (hright := (integerReciprocalDerivativeRemainder k a z ha hz).property)
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw i.val i.property
  let J := ComplexRawQuotient.ofRaw j.val j.property
  change ComplexRawQuotient.ofRaw (integerAffine 1 k a.val) (integerShiftScalar a k).property * I = 1 at hi
  change ComplexRawQuotient.ofRaw (integerAffine 1 k z.val) (integerShiftScalar z k).property * J = 1 at hj
  rw [integerAffine_class] at hi hj
  change (((1:Int):ComplexRawQuotient.Value)*A+k)*I=1 at hi
  change (((1:Int):ComplexRawQuotient.Value)*Z+k)*J=1 at hj
  change (-(J*J)- -(I*I))-((I*(I*I)+I*(I*I))*(Z-A)) =
    -((I*(((I*I)*J)*((Z-A)*(Z-A)))+I*(((I*I)*J)*((Z-A)*(Z-A))))+(J-I)*(J-I))
  grind only

end ComputableAnalysis.ModularForms
