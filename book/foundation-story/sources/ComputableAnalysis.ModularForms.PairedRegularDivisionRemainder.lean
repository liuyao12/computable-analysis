import ComputableAnalysis.ModularForms.PairedRegularDivisionDerivative

/-! Exact quadratic remainder for the reciprocal quadratic terms. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedRegularDivisionRemainder (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z) (n : Nat) : Scalar :=
  let i := (pairedSmallDiskLiteralInverseMap n).eval a ha
  let j := (pairedSmallDiskLiteralInverseMap n).eval z hz
  let h : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
  let d : Scalar := ⟨sub (mul z.val z.val) (mul a.val a.val),
    sub_valid (mul_valid z.property z.property) (mul_valid a.property a.property)⟩
  let ds := DomainFunctions.scalarProduct (DomainFunctions.scalarProduct d d) j
  let hs := DomainFunctions.scalarProduct h h
  let r := DomainFunctions.scalarProduct (DomainFunctions.scalarProduct i i)
    ⟨sub ds.val hs.val,sub_valid ds.property hs.property⟩
  DomainFunctions.scalarSum r r

theorem pairedRegularDivisionTermMap_remainder (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z) (n : Nat) :
    (DomainFunctions.remainder (pairedRegularDivisionTermMap n) a ha
      (pairedRegularDivisionDerivativeTerm a ha n) z hz).Equiv
      (pairedRegularDivisionRemainder a z ha hz n).val := by
  let da := pairedSmallDisk_domain a (1/4) (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ a ha)
  let dz := pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ z hz)
  have hai := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (pairedLiteralDenominator a (pairedIntegerSquare (n+1))).property
      ((pairedSmallDiskLiteralInverseMap n).eval a ha).property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse _ (da n))
  have hzj := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (pairedLiteralDenominator z (pairedIntegerSquare (n+1))).property
      ((pairedSmallDiskLiteralInverseMap n).eval z hz).property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse _ (dz n))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := DomainFunctions.remainder_valid _ _ _ _ _ _)
    (hright := (pairedRegularDivisionRemainder a z ha hz n).property)
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw ((pairedSmallDiskLiteralInverseMap n).eval a ha).val
    ((pairedSmallDiskLiteralInverseMap n).eval a ha).property
  let J := ComplexRawQuotient.ofRaw ((pairedSmallDiskLiteralInverseMap n).eval z hz).val
    ((pairedSmallDiskLiteralInverseMap n).eval z hz).property
  let T := ComplexRawQuotient.ofQComplex ⟨pairedIntegerSquare (n+1),0⟩
  change (A*A-T)*I=1 at hai
  change (Z*Z-T)*J=1 at hzj
  change ((J+J)-(I+I))-((-(I*I)*(A+A)+(-(I*I)*(A+A)))*(Z-A)) =
    (I*I)*(((Z*Z-A*A)*(Z*Z-A*A))*J-(Z-A)*(Z-A))+
    (I*I)*(((Z*Z-A*A)*(Z*Z-A*A))*J-(Z-A)*(Z-A))
  grind only

end ComputableAnalysis.ModularForms
