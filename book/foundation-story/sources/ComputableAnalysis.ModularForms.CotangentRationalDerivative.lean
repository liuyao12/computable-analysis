import ComputableAnalysis.ModularForms.CotangentRationalKernel

/-! Exact derivative and differential identity on the full rational-kernel domain. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def cotangentRationalDerivative (z : Scalar) (hz : cotangentRationalMap.domain z) : Scalar :=
  scalarSum (DomainFunctions.scalarProduct (nomeRationalInverseMap.eval z hz) (nomeRationalInverseMap.eval z hz))
    (DomainFunctions.scalarProduct (nomeRationalInverseMap.eval z hz) (nomeRationalInverseMap.eval z hz))

theorem cotangentRationalMap_derivative (z : Scalar) (hz : cotangentRationalMap.domain z) :
    (cotangentRationalMap_holomorphic.derivative z hz).val.Equiv (cotangentRationalDerivative z hz).val := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator z).property (nomeRationalInverseMap.eval z hz).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse _ (compose_outer_mem hz))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (cotangentRationalMap_holomorphic.derivative z hz).property)
    (hright := (cotangentRationalDerivative z hz).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw (nomeRationalInverseMap.eval z hz).val (nomeRationalInverseMap.eval z hz).property
  change (1-Z)*I=1 at hi
  change ((-(I*I))*(-1))*(1+1*Z)+I*1=I*I+I*I
  grind only

def cotangentRationalMap_hasDerivativeAt (z : Scalar) (hz : cotangentRationalMap.domain z) :
    HasDerivativeAt cotangentRationalMap z hz (cotangentRationalDerivative z hz) :=
  (cotangentRationalMap_holomorphic.atPoint z hz).congrDerivative (cotangentRationalMap_derivative z hz)

theorem cotangentRationalMap_differential_identity (z : Scalar) (hz : cotangentRationalMap.domain z) :
    (add (mul z.val (cotangentRationalDerivative z hz).val)
      (mul z.val (cotangentRationalDerivative z hz).val)).Equiv
      (sub (mul (cotangentRationalMap.eval z hz).val (cotangentRationalMap.eval z hz).val)
        (ofQComplex QComplex.one)) := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator z).property (nomeRationalInverseMap.eval z hz).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse _ (compose_outer_mem hz))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := add_valid (mul_valid z.property (cotangentRationalDerivative z hz).property)
      (mul_valid z.property (cotangentRationalDerivative z hz).property))
    (hright := sub_valid (mul_valid (cotangentRationalMap.eval z hz).property
      (cotangentRationalMap.eval z hz).property) (ofQComplex_valid _))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw (nomeRationalInverseMap.eval z hz).val (nomeRationalInverseMap.eval z hz).property
  change (1-Z)*I=1 at hi
  change Z*(I*I+I*I)+Z*(I*I+I*I)=(I*(1+1*Z))*(I*(1+1*Z))-1
  grind only

end ComputableAnalysis.ModularForms
