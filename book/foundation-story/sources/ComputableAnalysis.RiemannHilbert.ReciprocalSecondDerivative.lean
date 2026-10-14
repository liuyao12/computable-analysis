import ComputableAnalysis.RiemannHilbert.DomainHolomorphicAlgebra
import ComputableAnalysis.RiemannHilbert.DomainDerivativeInvariance
import ComputableAnalysis.RiemannHilbert.ReciprocalHolomorphic

/-! The derivative of the actual reciprocal is itself holomorphic.
Its second derivative is proved from the quantitative product rule. -/
namespace ComputableAnalysis.RiemannHilbert.ReciprocalHolomorphic
open ComplexRaw FunctionTheory NonzeroBoxSearch RepresentedReciprocal DomainFunctions

def derivativeFunction : DomainFunctions.Map := derivativeMap function holomorphic

def derivativeHolomorphic : Holomorphic derivativeFunction :=
  (holomorphic.productOn holomorphic (fun _ hz => hz)).negate

theorem derivativeFunction_eval (z : Scalar) (hz : Nonzero z) :
    derivativeFunction.eval z hz = ReciprocalDifference.derivative z hz := rfl

def secondDerivative (z : Scalar) (hz : Nonzero z) : Scalar :=
  let r := inverse z hz
  let cube := scalarProduct (scalarProduct r r) r
  scalarSum cube cube

theorem secondDerivative_formula (z : Scalar) (hz : Nonzero z) :
    (derivativeHolomorphic.derivative z hz).val.Equiv (secondDerivative z hz).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (derivativeHolomorphic.derivative z hz).property)
    (hright := (secondDerivative z hz).property)
  let R := ComplexRawQuotient.ofRaw (inverse z hz).val (inverse z hz).property
  change -((-(R*R))*R + R*(-(R*R))) = (R*R)*R+(R*R)*R
  grind

def hasSecondDerivativeAt (z : Scalar) (hz : Nonzero z) :
    HasDerivativeAt derivativeFunction z hz (secondDerivative z hz) :=
  (derivativeHolomorphic.atPoint z hz).congrDerivative (secondDerivative_formula z hz)

theorem secondDerivative_congr (z w : Scalar) (hz : Nonzero z) (hw : Nonzero w)
    (hzw : z.val.Equiv w.val) : (secondDerivative z hz).val.Equiv (secondDerivative w hw).val := by
  exact equiv_trans (secondDerivative z hz).property (derivativeHolomorphic.derivative z hz).property
    (secondDerivative w hw).property (equiv_symm (secondDerivative_formula z hz))
    (equiv_trans (derivativeHolomorphic.derivative z hz).property (derivativeHolomorphic.derivative w hw).property
      (secondDerivative w hw).property (derivativeHolomorphic.derivative_congr z w hz hw hzw) (secondDerivative_formula w hw))

end ComputableAnalysis.RiemannHilbert.ReciprocalHolomorphic
