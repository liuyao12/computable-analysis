import ComputableAnalysis.ModularForms.NomeRationalCotangent
import ComputableAnalysis.ModularForms.ExponentialDerivative

/-! Actual chain-rule derivative and differential equation for the nome rational kernel. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem nome_derivative_value (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (nome_holomorphic.derivative z hz).val.Equiv (mul (nome.eval z hz).val nomeSlope.val) :=
  mul_equiv (entireExponential_holomorphic.derivative (nomeExponentMap.eval z hz) trivial).property
    (nome.eval z hz).property nomeSlope.property nomeSlope.property
    (entireExponential_derivative_value (nomeExponentMap.eval z hz)) (equiv_refl _ nomeSlope.property)

def nomeRationalCotangentDerivative (z : Scalar) (hz : nomeRationalCotangentMap.domain z) : Scalar :=
  DomainFunctions.scalarProduct
    (cotangentRationalDerivative (nome.eval z (compose_inner_mem hz)) (compose_outer_mem hz))
    (DomainFunctions.scalarProduct (nome.eval z (compose_inner_mem hz)) nomeSlope)

theorem nomeRationalCotangentMap_derivative (z : Scalar) (hz : nomeRationalCotangentMap.domain z) :
    (nomeRationalCotangentMap_holomorphic.derivative z hz).val.Equiv
      (nomeRationalCotangentDerivative z hz).val :=
  mul_equiv
    (cotangentRationalMap_holomorphic.derivative (nome.eval z (compose_inner_mem hz)) (compose_outer_mem hz)).property
    (cotangentRationalDerivative (nome.eval z (compose_inner_mem hz)) (compose_outer_mem hz)).property
    (nome_holomorphic.derivative z (compose_inner_mem hz)).property
    (DomainFunctions.scalarProduct (nome.eval z (compose_inner_mem hz)) nomeSlope).property
    (cotangentRationalMap_derivative _ _) (nome_derivative_value z (compose_inner_mem hz))

def nomeRationalCotangentMap_hasDerivativeAt (z : Scalar) (hz : nomeRationalCotangentMap.domain z) :
    HasDerivativeAt nomeRationalCotangentMap z hz (nomeRationalCotangentDerivative z hz) :=
  (nomeRationalCotangentMap_holomorphic.atPoint z hz).congrDerivative
    (nomeRationalCotangentMap_derivative z hz)

theorem nomeRationalCotangent_differential_identity (z : Scalar) (hz : nomeRationalCotangentMap.domain z) :
    (add (nomeRationalCotangentDerivative z hz).val (nomeRationalCotangentDerivative z hz).val).Equiv
      (mul nomeSlope.val (sub (mul (nomeRationalCotangentMap.eval z hz).val
        (nomeRationalCotangentMap.eval z hz).val) (ofQComplex QComplex.one))) := by
  let q := nome.eval z (compose_inner_mem hz)
  let hq := compose_outer_mem hz
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator q).property (nomeRationalInverseMap.eval q hq).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse _ (compose_outer_mem hq))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := add_valid (nomeRationalCotangentDerivative z hz).property (nomeRationalCotangentDerivative z hz).property)
    (hright := mul_valid nomeSlope.property (sub_valid
      (mul_valid (nomeRationalCotangentMap.eval z hz).property (nomeRationalCotangentMap.eval z hz).property)
      (ofQComplex_valid _)))
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  let A := ComplexRawQuotient.ofRaw nomeSlope.val nomeSlope.property
  let I := ComplexRawQuotient.ofRaw (nomeRationalInverseMap.eval q hq).val (nomeRationalInverseMap.eval q hq).property
  change (1-Q)*I=1 at hi
  change (I*I+I*I)*(Q*A)+(I*I+I*I)*(Q*A)=A*((I*(1+1*Q))*(I*(1+1*Q))-1)
  grind only

end ComputableAnalysis.ModularForms
