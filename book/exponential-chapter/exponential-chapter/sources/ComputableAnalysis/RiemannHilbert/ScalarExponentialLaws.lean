import ComputableAnalysis.RiemannHilbert.ExponentialParameterScaling
import ComputableAnalysis.RiemannHilbert.ExponentialScalarOperators
import ComputableAnalysis.RiemannHilbert.ExponentialCommutingSum
import ComputableAnalysis.RiemannHilbert.RelativeLogarithmExponential

/-! Agreement of the two constructed scalar exponentials, the exact
addition law, and scalar branch propagation through normalized logarithm
charts. Arbitrary represented inputs are retained throughout. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem LocalODE DomainFunctions NonzeroBoxSearch
set_option maxHeartbeats 1000000

theorem scalarExponential_parameter (a : Scalar) :
    (scalarExponential a).val.Equiv
      (((value (ValueMap.identity : ValueMap (Fiber 1) (Fiber 1)) (IsLinear.identity 1) a).eval ScalarNeumannInverse.unit).val 0) := by
  let I : ValueMap (Fiber 1) (Fiber 1) := ValueMap.identity
  have hm : (OperatorPower.scaled I a).Equiv (Fiber.scaleMap a) := fun _ => Setoid.refl _
  have h1 : (value (Fiber.scaleMap a) (Fiber.scaleMap_linear a) MatrixLogarithm.unit).eval ScalarNeumannInverse.unit ≈
      (value I (IsLinear.identity 1) (parameterProduct a MatrixLogarithm.unit)).eval ScalarNeumannInverse.unit :=
    Setoid.trans (value_congr _ _ (Fiber.scaleMap_linear a) (OperatorPower.scaled_linear I (IsLinear.identity 1) a)
      (ValueMap.equiv_symm hm) MatrixLogarithm.unit MatrixLogarithm.unit (equiv_refl _ MatrixLogarithm.unit.property)
      ScalarNeumannInverse.unit ScalarNeumannInverse.unit (Setoid.refl _))
      (value_scaled_operator I (IsLinear.identity 1) a MatrixLogarithm.unit ScalarNeumannInverse.unit)
  exact Setoid.trans h1 (value_congr I I (IsLinear.identity 1) (IsLinear.identity 1) (ValueMap.equiv_refl I)
    (parameterProduct a MatrixLogarithm.unit) a (mul_one_equiv _ a.property)
    ScalarNeumannInverse.unit ScalarNeumannInverse.unit (Setoid.refl _)) 0

theorem scalarExponential_local_agreement (a : Scalar) :
    (scalarExponential a).val.Equiv (LocalLogarithm.exponential a).val := scalarExponential_parameter a

theorem scalar_operator_sum (a b : Scalar) :
    (sumResidue (Fiber.scaleMap (n := n) a) (Fiber.scaleMap b)).Equiv (Fiber.scaleMap (scalarSum a b)) :=
  fun x i => equiv_symm (add_mul_equiv a.val b.val (x.val i) a.property b.property (x.property i))

/-- The actual represented scalar exponential turns sums into products. -/
theorem scalarExponential_add (a b : Scalar) :
    (scalarExponential (scalarSum a b)).val.Equiv (mul (scalarExponential a).val (scalarExponential b).val) := by
  let A := Fiber.scaleMap (n := 1) a
  let B := Fiber.scaleMap (n := 1) b
  let S := sumResidue A B
  have hA := Fiber.scaleMap_linear (n := 1) a
  have hB := Fiber.scaleMap_linear (n := 1) b
  have hS := sumResidue_linear A B hA hB
  have hs : (value (Fiber.scaleMap (n := 1) (scalarSum a b)) (Fiber.scaleMap_linear _) MatrixLogarithm.unit).eval
      ScalarNeumannInverse.unit ≈ (value A hA MatrixLogarithm.unit).eval ((value B hB MatrixLogarithm.unit).eval ScalarNeumannInverse.unit) :=
    Setoid.trans (value_congr _ S (Fiber.scaleMap_linear _) hS (ValueMap.equiv_symm (scalar_operator_sum a b))
      MatrixLogarithm.unit MatrixLogarithm.unit (equiv_refl _ MatrixLogarithm.unit.property)
      ScalarNeumannInverse.unit ScalarNeumannInverse.unit (Setoid.refl _))
      (value_commuting_sum A B hA hB (fun x => Setoid.symm (hB.2 a x)) MatrixLogarithm.unit ScalarNeumannInverse.unit)
  exact Setoid.trans hs (value_scalar_operator a ((value B hB MatrixLogarithm.unit).eval ScalarNeumannInverse.unit)) 0

theorem scalarExponential_log (z : Scalar) (hz : interior LocalLogarithm.radius.val z) :
    (scalarExponential (LocalLogarithm.function.eval z hz)).val.Equiv (LocalLogarithm.onePlus z).val :=
  equiv_trans (scalarExponential (LocalLogarithm.function.eval z hz)).property
    (LocalLogarithm.exponential (LocalLogarithm.function.eval z hz)).property (LocalLogarithm.onePlus z).property
    (scalarExponential_local_agreement _) (LocalLogarithm.exponential_log z hz)

theorem scalarExponential_relative (c : Scalar) (hc : Nonzero c) (z : Scalar) (hz : RelativeLogarithm.domain c hc z) :
    (scalarExponential ((RelativeLogarithm.function c hc).eval z hz)).val.Equiv
      (mul (RepresentedReciprocal.inverse c hc).val z.val) :=
  equiv_trans (scalarExponential ((RelativeLogarithm.function c hc).eval z hz)).property
    (LocalLogarithm.exponential ((RelativeLogarithm.function c hc).eval z hz)).property
    (mul_valid (RepresentedReciprocal.inverse c hc).property z.property)
    (scalarExponential_local_agreement _) (RelativeLogarithm.exponential_value c hc z hz)

def propagatedBranch (c : Scalar) (hc : Nonzero c) (a z : Scalar) (hz : RelativeLogarithm.domain c hc z) : Scalar :=
  scalarSum a ((RelativeLogarithm.function c hc).eval z hz)

/-- A justified scalar branch at a center extends by the actual local
Taylor logarithm. No scalar branch at the endpoint is assumed. -/
theorem propagatedBranch_exponential (c : Scalar) (hc : Nonzero c) (a : Scalar)
    (ha : (scalarExponential a).val.Equiv c.val) (z : Scalar) (hz : RelativeLogarithm.domain c hc z) :
    (scalarExponential (propagatedBranch c hc a z hz)).val.Equiv z.val := by
  have he := scalarExponential_add a ((RelativeLogarithm.function c hc).eval z hz)
  have hm := mul_equiv (scalarExponential a).property c.property
    (scalarExponential ((RelativeLogarithm.function c hc).eval z hz)).property
    (mul_valid (RepresentedReciprocal.inverse c hc).property z.property) ha (scalarExponential_relative c hc z hz)
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid c.property (RepresentedReciprocal.inverse c hc).property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse c hc)
  have hcancel : (mul c.val (mul (RepresentedReciprocal.inverse c hc).val z.val)).Equiv z.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid c.property (mul_valid (RepresentedReciprocal.inverse c hc).property z.property)) (hright := z.property)
    let C := ComplexRawQuotient.ofRaw c.val c.property
    let R := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse c hc).val (RepresentedReciprocal.inverse c hc).property
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change C*R=1 at hi
    change C*(R*Z)=Z
    grind only
  exact equiv_trans (scalarExponential (propagatedBranch c hc a z hz)).property
    (mul_valid c.property (mul_valid (RepresentedReciprocal.inverse c hc).property z.property)) z.property
    (equiv_trans (scalarExponential (propagatedBranch c hc a z hz)).property
      (mul_valid (scalarExponential a).property (scalarExponential ((RelativeLogarithm.function c hc).eval z hz)).property)
      (mul_valid c.property (mul_valid (RepresentedReciprocal.inverse c hc).property z.property)) he hm) hcancel

end ComputableAnalysis.RiemannHilbert.MatrixExponential
