import ComputableAnalysis.ModularForms.RationalCenterApproximation
import ComputableAnalysis.ModularForms.ExponentialContinuity

/-! One common chart and shrinking exponential errors for all stage centers. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert LocalODE

def rationalCenter (z : Scalar) (n : Nat) : Scalar :=
  ⟨ofQComplex (z.val.compute n).center,ofQComplex_valid _⟩

theorem rationalCenter_bound (z : Scalar) (n : Nat) :
    Small (rationalCenter z n).val (boxCoordinateBound (z.val.compute 0)) := by
  have hb := boxCoordinateBound_bounds (z.val.compute 0)
  have hc := QBox.center_mem (valid_ordered z.property n)
  have hn := valid_nestedIn z.property (show 0 ≤ n by omega)
  have hpoint : (z.val.compute 0).lo ≤ (z.val.compute n).center ∧
      (z.val.compute n).center ≤ (z.val.compute 0).hi :=
    ⟨QComplex.le_trans hn.1 hc.1, QComplex.le_trans hc.2 hn.2⟩
  simp only [QComplex.le_def] at hpoint
  refine ⟨?_,?_,?_,?_⟩ <;> intro i j
  · change -boxCoordinateBound (z.val.compute 0) ≤ (z.val.compute n).center.re
    grind
  · change (z.val.compute n).center.re ≤ boxCoordinateBound (z.val.compute 0)
    grind
  · change -boxCoordinateBound (z.val.compute 0) ≤ (z.val.compute n).center.im
    grind
  · change (z.val.compute n).center.im ≤ boxCoordinateBound (z.val.compute 0)
    grind

theorem rationalCenter_chart (z : Scalar) (n : Nat) :
    (exponentialChart (exponentialInputRadius z)).domain (rationalCenter z n) := by
  refine ⟨boxCoordinateBound (z.val.compute 0),boxCoordinateBound_nonneg _,?_,rationalCenter_bound z n⟩
  change boxCoordinateBound (z.val.compute 0) < boxCoordinateBound (z.val.compute 0)+1
  grind

def exponentialCenterError (z : Scalar) (n : Nat) : Rat :=
  16*exponentialBudget (exponentialRatio (exponentialInputRadius z))*
    (exponentialRatio (exponentialInputRadius z))^2*centerError z.val n

theorem exponential_center_error (z : Scalar) (n : Nat) :
    Small (sub (entireExponentialValue z).val
      (entireExponentialValue (rationalCenter z n)).val) (exponentialCenterError z n) :=
  entireExponential_lipschitz (exponentialInputRadius z) (rationalCenter z n) z
    (rationalCenter_chart z n) (exponentialInputRadius_mem z)
    (centerError z.val n) (centerError_nonnegative z.val z.property n)
    (rational_center_error z.val z.property n)

theorem exponentialCenterError_shrinks (z : Scalar) :
    ShrinksToZero (exponentialCenterError z) := by
  have hC := exponentialBudget_nonnegative _ (exponentialRatio_positive (exponentialInputRadius z))
  have hK := Rat.le_of_lt (exponentialRatio_positive (exponentialInputRadius z))
  exact SeriesLimitLaws.shrinks_scale _ (centerError_shrinks z.val z.property) _
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hC) (Rat.pow_nonneg hK))

end ComputableAnalysis.ModularForms
