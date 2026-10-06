import ComputableAnalysis.ModularForms.EntireExponential
import ComputableAnalysis.RiemannHilbert.ScalarExponentialLaws
import ComputableAnalysis.RiemannHilbert.ExponentialPowerFormula

/-! The factorial-series exponential used for modular forms agrees with the
constructed exponential used by local logarithm charts, at every represented
complex input. This supplies an exact bridge, independent of chart budgets. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert LocalSystem LocalODE
set_option maxHeartbeats 1000000

private def identityOperator : ValueMap (Fiber 1) (Fiber 1) := ValueMap.identity

private theorem identityPower (k : Nat) :
    (Neumann.power identityOperator k).eval ScalarNeumannInverse.unit ≈ ScalarNeumannInverse.unit := by
  induction k with
  | zero => exact Setoid.refl _
  | succ k ih => exact ih

private theorem identityCoefficient (k : Nat) :
    ((MatrixExponential.coefficient identityOperator ScalarNeumannInverse.unit k).val 0).Equiv
      (exponentialCoefficients k) := by
  have h := MatrixExponential.coefficient_factorial_power identityOperator (IsLinear.identity 1)
    ScalarNeumannInverse.unit k
  have hp := ratScale_congr (1/factorialRat k) (identityPower k)
  have he : (scaleRat (1/factorialRat k) one).Equiv (exponentialCoefficients k) := by
    intro stage
    apply (compareAt_overlap_iff _ _ stage stage).mpr
    simp only [exponentialCoefficients, scaleRat, one, ofQComplex, QBox.scaleRat,
      QComplex.one, ite_self, Rat.mul_one, Rat.mul_zero]
    constructor <;> exact QComplex.le_refl _
  exact equiv_trans ((MatrixExponential.coefficient identityOperator ScalarNeumannInverse.unit k).property 0)
    (scaleRat_valid (ofQComplex_valid _)) (exponentialCoefficients_valid k)
    (equiv_trans ((MatrixExponential.coefficient identityOperator ScalarNeumannInverse.unit k).property 0)
      ((ratScale (1/factorialRat k) ((Neumann.power identityOperator k).eval ScalarNeumannInverse.unit)).property 0)
      (scaleRat_valid (ofQComplex_valid _)) (h 0) (hp 0)) he

theorem localLogarithm_exponential_agreement (z : Scalar) :
    (LocalLogarithm.exponential z).val.Equiv (entireExponentialValue z).val := by
  let A := identityOperator
  let R := MatrixExponential.pointRadius z
  let S := exponentialInputRadius z
  let M := MatrixExponential.discBudget A R.val
  let K := MatrixExponential.rate R.val
  let C := 2*M*LocalSystem.initialBound ScalarNeumannInverse.unit
  have hM := MatrixExponential.discBudget_nonneg A R.val
  have hK := Rat.le_of_lt (MatrixExponential.rate_pos R.val (Rat.le_of_lt R.property))
  have hR := Rat.le_of_lt R.property
  have hlocal : 2*K*R.val ≤ (1:Rat)/2 := by
    have h := MatrixExponential.rate_small R.val hR
    have hn := Rat.mul_nonneg hK hR
    dsimp [K]; grind
  exact coefficientSum_congr_of_bounds _ _ z.val z.val
    (fun k => (MatrixExponential.coefficient identityOperator ScalarNeumannInverse.unit k).property 0)
    exponentialCoefficients_valid z.property z.property
    identityCoefficient (equiv_refl _ z.property)
    C K R.val (exponentialBudget (exponentialRatio S)) (exponentialRatio S) S.val
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hM) (LocalSystem.initialBound_nonneg _))
    hK hR (exponentialBudget_nonnegative _ (exponentialRatio_positive S))
    (Rat.le_of_lt (exponentialRatio_positive S)) (Rat.le_of_lt S.property)
    (fun k => operatorCoefficient_bound (MatrixExponential.coefficientMap A) M K
      (LocalSystem.initialBound ScalarNeumannInverse.unit) (LocalSystem.initialBound_nonneg _)
      (MatrixExponential.disc_majorant A (IsLinear.identity 1) R.val hR)
      ScalarNeumannInverse.unit (LocalSystem.initialBound_valid _) k 0)
    (exponentialCoefficients_small _ (exponentialRatio_positive S))
    (interior_bound R.val z (MatrixExponential.pointRadius_inside z))
    (interior_bound S.val z (exponentialInputRadius_mem z)) hlocal
    (by have h := exponentialRatio_local S
        have hn := Rat.mul_nonneg (Rat.le_of_lt (exponentialRatio_positive S)) (Rat.le_of_lt S.property)
        grind)

/-- The independent matrix scalar exponential also agrees with the modular
form evaluator on every represented input. -/
theorem scalarExponential_agreement (z : Scalar) :
    (MatrixExponential.scalarExponential z).val.Equiv (entireExponentialValue z).val :=
  equiv_trans (MatrixExponential.scalarExponential z).property
    (LocalLogarithm.exponential z).property (entireExponentialValue z).property
    (MatrixExponential.scalarExponential_local_agreement z) (localLogarithm_exponential_agreement z)

/-- The actual Taylor logarithm is a local right inverse for the exponential
used in modular forms. -/
theorem entireExponential_localLogarithm (z : Scalar)
    (hz : interior LocalLogarithm.radius.val z) :
    (entireExponentialValue (LocalLogarithm.function.eval z hz)).val.Equiv
      (LocalLogarithm.onePlus z).val :=
  equiv_trans (entireExponentialValue (LocalLogarithm.function.eval z hz)).property
    (LocalLogarithm.exponential (LocalLogarithm.function.eval z hz)).property
    (LocalLogarithm.onePlus z).property
    (equiv_symm (localLogarithm_exponential_agreement _)) (LocalLogarithm.exponential_log z hz)

/-- A normalized logarithm chart exponentiates to the quotient by its center. -/
theorem entireExponential_relativeLogarithm (c : Scalar) (hc : NonzeroBoxSearch.Nonzero c)
    (z : Scalar) (hz : RelativeLogarithm.domain c hc z) :
    (entireExponentialValue ((RelativeLogarithm.function c hc).eval z hz)).val.Equiv
      (mul (RepresentedReciprocal.inverse c hc).val z.val) :=
  equiv_trans (entireExponentialValue ((RelativeLogarithm.function c hc).eval z hz)).property
    (LocalLogarithm.exponential ((RelativeLogarithm.function c hc).eval z hz)).property
    (mul_valid (RepresentedReciprocal.inverse c hc).property z.property)
    (equiv_symm (localLogarithm_exponential_agreement _))
    (RelativeLogarithm.exponential_value c hc z hz)

/-- A supplied logarithm value at the center extends by a constructed Taylor
chart. The endpoint exponential identity is proved, not supplied. -/
theorem entireExponential_propagatedLogarithm (c : Scalar) (hc : NonzeroBoxSearch.Nonzero c)
    (a : Scalar) (ha : (entireExponentialValue a).val.Equiv c.val)
    (z : Scalar) (hz : RelativeLogarithm.domain c hc z) :
    (entireExponentialValue (MatrixExponential.propagatedBranch c hc a z hz)).val.Equiv z.val :=
  equiv_trans (entireExponentialValue (MatrixExponential.propagatedBranch c hc a z hz)).property
    (MatrixExponential.scalarExponential (MatrixExponential.propagatedBranch c hc a z hz)).property
    z.property (equiv_symm (scalarExponential_agreement _))
    (MatrixExponential.propagatedBranch_exponential c hc a
      (equiv_trans (MatrixExponential.scalarExponential a).property
        (entireExponentialValue a).property c.property (scalarExponential_agreement a) ha) z hz)

end ComputableAnalysis.ModularForms
