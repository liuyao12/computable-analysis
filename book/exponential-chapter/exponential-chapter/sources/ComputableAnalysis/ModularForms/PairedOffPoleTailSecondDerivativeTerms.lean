import ComputableAnalysis.ModularForms.PairedOffPoleTailDerivativeTermHolomorphic

/-! Actual second derivatives of the rational tail terms on their full cutoff disk. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private def twice (x : Scalar) : Scalar := scalarSum x x

def pairedOffPoleTailSecondDerivativeTerm (B n : Nat) (z : Scalar)
    (hz : LocalODE.interior (B:Rat) z) : Scalar :=
  let i := pairedOffPoleTailInverse B n z hz
  let a := scalarNeg (scalarProduct z (scalarProduct i i))
  let b := scalarProduct (scalarProduct (scalarProduct z z) z)
    (scalarProduct i (scalarProduct i i))
  scalarSum (scalarSum (twice (twice a)) (twice (twice (twice a))))
    (twice (twice (twice (twice b))))

theorem pairedOffPoleTailInverseMap_derivative (B n : Nat) (z : Scalar)
    (hz : LocalODE.interior (B:Rat) z) :
    ((pairedOffPoleTailInverseMap_holomorphic B n).derivative z hz).val.Equiv
      (neg (mul (mul (pairedOffPoleTailInverse B n z hz).val
        (pairedOffPoleTailInverse B n z hz).val) (add z.val z.val))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((pairedOffPoleTailInverseMap_holomorphic B n).derivative z hz).property)
    (hright := neg_valid (mul_valid (mul_valid (pairedOffPoleTailInverse B n z hz).property
      (pairedOffPoleTailInverse B n z hz).property) (add_valid z.property z.property)))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw (pairedOffPoleTailInverse B n z hz).val
    (pairedOffPoleTailInverse B n z hz).property
  change -(I*I)*(1*(1*(0+1*Z)+(0+1*Z)*1))= -((I*I)*(Z+Z))
  grind only

theorem pairedOffPoleTailDerivativeTermMap_derivative (B n : Nat) (z : Scalar)
    (hz : LocalODE.interior (B:Rat) z) :
    ((pairedOffPoleTailDerivativeTermMap_holomorphic B n).derivative z hz).val.Equiv
      (pairedOffPoleTailSecondDerivativeTerm B n z hz).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((pairedOffPoleTailDerivativeTermMap_holomorphic B n).derivative z hz).property)
    (hright := (pairedOffPoleTailSecondDerivativeTerm B n z hz).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw (pairedOffPoleTailInverse B n z hz).val
    (pairedOffPoleTailInverse B n z hz).property
  let A := ComplexRawQuotient.ofQComplex ⟨(2:Rat),0⟩
  let D := -(I*I)*(1*(1*(0+1*Z)+(0+1*Z)*1))
  let X := 0+A*Z
  let P := -(Z*(I*I))
  let Q := ((Z*Z)*Z)*(I*(I*I))
  change (D+D)+ -((D*I+I*D)*(X*X)+(I*I)*(A*X+X*A)) =
    (((P+P)+(P+P))+(((P+P)+(P+P))+((P+P)+(P+P))))+
    ((((Q+Q)+(Q+Q))+((Q+Q)+(Q+Q)))+(((Q+Q)+(Q+Q))+((Q+Q)+(Q+Q))))
  have htwo : A=((2:Int):ComplexRawQuotient.Value) := by
    simpa only [show ((2:Int):Rat)=2 by decide +kernel] using integer_constant (2:Int)
  dsimp only [D,X,P,Q]
  rw [htwo]
  grind only

def pairedOffPoleTailDerivativeTermMap_hasDerivativeAt (B n : Nat) (z : Scalar)
    (hz : LocalODE.interior (B:Rat) z) :
    HasDerivativeAt (pairedOffPoleTailDerivativeTermMap B n) z hz
      (pairedOffPoleTailSecondDerivativeTerm B n z hz) :=
  ((pairedOffPoleTailDerivativeTermMap_holomorphic B n).atPoint z hz).congrDerivative
    (pairedOffPoleTailDerivativeTermMap_derivative B n z hz)

end ComputableAnalysis.ModularForms
