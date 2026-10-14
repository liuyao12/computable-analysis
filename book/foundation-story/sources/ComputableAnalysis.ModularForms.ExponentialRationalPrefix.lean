import ComputableAnalysis.ModularForms.ExponentialCharts
import ComputableAnalysis.ComplexExponentialApproximation
import ComputableAnalysis.ComplexInterval

/-! The represented factorial prefixes coincide with the rational prefixes
used by the older exponential and rotation constructions. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem rational_power_compute (z : QComplex) (n stage : Nat) :
    (LocalODE.power (ofQComplex z) n).compute stage = QBox.point (QComplex.pow z n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change QBox.mul ((LocalODE.power (ofQComplex z) n).compute stage) (QBox.point z) = _
    rw [ih, QBox.mul_point]
    change QBox.point (QComplex.mul (QComplex.pow z n) z) =
      QBox.point (QComplex.mul z (QComplex.pow z n))
    exact congrArg QBox.point (QComplex.mul_comm_cert _ _)

theorem rational_exponential_term_compute (z : QComplex) (n stage : Nat) :
    (LocalODE.seriesTerm exponentialCoefficients (ofQComplex z) n).compute stage =
      QBox.point (ComplexSeries.expTerm z n) := by
  change QBox.mul (QBox.point ⟨1/factorialRat n,0⟩)
    ((LocalODE.power (ofQComplex z) n).compute stage) = _
  rw [rational_power_compute, QBox.mul_point]
  unfold ComplexSeries.expTerm QComplex.divRat QComplex.mul
  congr 1 <;> congr 1 <;> simp [Rat.div_def, Rat.mul_zero, Rat.zero_mul] <;> grind

theorem rational_exponential_prefix_compute (z : QComplex) (N stage : Nat) :
    (ScalarSeries.block (LocalODE.seriesTerm exponentialCoefficients (ofQComplex z)) 0 N).compute stage =
      QBox.point (ComplexExponentialApproximation.expPrefix z N) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change QBox.add
      ((ScalarSeries.block (LocalODE.seriesTerm exponentialCoefficients (ofQComplex z)) 0 N).compute stage)
      ((LocalODE.seriesTerm exponentialCoefficients (ofQComplex z) (0+N)).compute stage) = _
    rw [ih, Nat.zero_add, rational_exponential_term_compute, QBox.add_point,
      ComplexExponentialApproximation.expPrefix_succ]

end ComputableAnalysis.ModularForms
