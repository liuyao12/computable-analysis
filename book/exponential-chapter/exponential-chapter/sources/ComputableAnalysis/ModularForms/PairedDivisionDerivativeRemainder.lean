import ComputableAnalysis.ModularForms.PairedDivisionSecondDerivative
import ComputableAnalysis.ModularForms.PairedRegularDivisionRemainderBound

/-! Exact quadratic remainder decomposition for the first-derivative terms. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedDivisionDerivativeRemainder (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z) (n : Nat) : Scalar :=
  let i := (pairedSmallDiskLiteralInverseMap n).eval a ha
  let j := (pairedSmallDiskLiteralInverseMap n).eval z hz
  let h : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
  let d : Scalar := ⟨sub j.val i.val,sub_valid j.property i.property⟩
  let q : Scalar := ⟨sub (mul j.val j.val) (mul i.val i.val),
    sub_valid (mul_valid j.property j.property) (mul_valid i.property i.property)⟩
  let r := pairedRegularDivisionRemainder a z ha hz n
  let v := scalarNeg (scalarSum
    (DomainFunctions.scalarProduct a (scalarSum (DomainFunctions.scalarProduct i r)
      (DomainFunctions.scalarProduct d d)))
    (DomainFunctions.scalarProduct h q))
  scalarSum (scalarSum v v) (scalarSum v v)

theorem pairedDivisionDerivativeTermMap_remainder (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z) (n : Nat) :
    (DomainFunctions.remainder (pairedDivisionDerivativeTermMap n) a ha
      (pairedDivisionSecondDerivativeTerm a ha n) z hz).Equiv
      (pairedDivisionDerivativeRemainder a z ha hz n).val := by
  let da := pairedSmallDisk_domain a (1/4) (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ a ha)
  let dz := pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ z hz)
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
    (hright := (pairedDivisionDerivativeRemainder a z ha hz n).property)
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw ((pairedSmallDiskLiteralInverseMap n).eval a ha).val
    ((pairedSmallDiskLiteralInverseMap n).eval a ha).property
  let J := ComplexRawQuotient.ofRaw ((pairedSmallDiskLiteralInverseMap n).eval z hz).val
    ((pairedSmallDiskLiteralInverseMap n).eval z hz).property
  let T := ComplexRawQuotient.ofQComplex ⟨pairedIntegerSquare (n+1),0⟩
  change (A*A-T)*I=1 at hai
  change (Z*Z-T)*J=1 at hzj
  let r := (I*I)*(((Z*Z-A*A)*(Z*Z-A*A))*J-(Z-A)*(Z-A))
  let v := -(A*(I*(r+r)+(J-I)*(J-I))+(Z-A)*(J*J-I*I))
  change ((-(J*J)*((0+1*Z)+(0+1*Z)))+(-(J*J)*((0+1*Z)+(0+1*Z))))-
    ((-(I*I)*((0+1*A)+(0+1*A)))+(-(I*I)*((0+1*A)+(0+1*A))))-
    ((((-(I*I)+-(I*I))+(-(I*I)+-(I*I)))+
      (((((A*A)*(I*(I*I))+(A*A)*(I*(I*I)))+((A*A)*(I*(I*I))+(A*A)*(I*(I*I))))+
        (((A*A)*(I*(I*I))+(A*A)*(I*(I*I)))+((A*A)*(I*(I*I))+(A*A)*(I*(I*I)))))+
       ((((A*A)*(I*(I*I))+(A*A)*(I*(I*I)))+((A*A)*(I*(I*I))+(A*A)*(I*(I*I))))+
        (((A*A)*(I*(I*I))+(A*A)*(I*(I*I)))+((A*A)*(I*(I*I))+(A*A)*(I*(I*I)))))))*(Z-A)) = (v+v)+(v+v)
  dsimp [v,r]
  grind only

end ComputableAnalysis.ModularForms
