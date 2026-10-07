import ComputableAnalysis.ModularForms.PairedOffPoleTailSecondDerivativeContinuity
import ComputableAnalysis.ModularForms.PairedOffPoleTailTermRemainderBound

/-! Explicit quadratic remainder decomposition for the actual derivative tail terms. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private def difference (x y : Scalar) : Scalar := ⟨sub x.val y.val,sub_valid x.property y.property⟩
private def twice (x : Scalar) : Scalar := scalarSum x x

def pairedOffPoleTailDerivativeRemainder (B n : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z) : Scalar :=
  let i := pairedOffPoleTailInverse B n a ha
  let j := pairedOffPoleTailInverse B n z hz
  let r := pairedOffPoleTailInverseRemainder B n a z ha hz
  let h := difference z a
  let d := difference j i
  let ir := scalarProduct i r
  let p := scalarSum
    (scalarSum
      (scalarProduct (scalarProduct a a) (scalarSum (twice ir) (scalarProduct d d)))
      (scalarProduct (scalarProduct i i) (scalarProduct h h)))
    (scalarProduct (difference (scalarProduct z z) (scalarProduct a a))
      (difference (scalarProduct j j) (scalarProduct i i)))
  difference (twice r) (twice (twice p))

theorem pairedOffPoleTailDerivativeTerm_remainder_identity (B n : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z) :
    (DomainFunctions.remainder (pairedOffPoleTailDerivativeTermMap B n) a ha
      (pairedOffPoleTailSecondDerivativeTerm B n a ha) z hz).Equiv
      (pairedOffPoleTailDerivativeRemainder B n a z ha hz).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := DomainFunctions.remainder_valid _ _ _ _ _ _)
    (hright := (pairedOffPoleTailDerivativeRemainder B n a z ha hz).property)
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw (pairedOffPoleTailInverse B n a ha).val
    (pairedOffPoleTailInverse B n a ha).property
  let J := ComplexRawQuotient.ofRaw (pairedOffPoleTailInverse B n z hz).val
    (pairedOffPoleTailInverse B n z hz).property
  let L := -(A*(I*I))
  let Q := ((A*A)*A)*(I*(I*I))
  let S := (((L+L)+(L+L))+(((L+L)+(L+L))+((L+L)+(L+L))))+
    ((((Q+Q)+(Q+Q))+((Q+Q)+(Q+Q)))+(((Q+Q)+(Q+Q))+((Q+Q)+(Q+Q))))
  let h := Z-A
  let d := J-I
  let r := d-(-((I*I)*(A+A)))*h
  let p := (A*A)*((I*r+I*r)+d*d)+(I*I)*(h*h)+(Z*Z-A*A)*(J*J-I*I)
  change (((J+J)-((Z+Z)*(Z+Z))*(J*J))-((I+I)-((A+A)*(A+A))*(I*I)))-S*h=
    (r+r)-((p+p)+(p+p))
  dsimp only [S,L,Q,h,d,r,p]
  grind only

end ComputableAnalysis.ModularForms
