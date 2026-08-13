import ComputableAnalysis.RotationSeries

/-!
# A finite quarter-turn certificate

The rational input `355/226` is a finite approximation to `pi/2`.  The
factorial rotation evaluator turns it into a rational complex box.  The
certificates below say that the unit imaginary point lies in those boxes at
several explicit stages.  This is a finite de Moivre/Euler-route checkpoint;
it does not identify a completed exponential with a geometric endpoint.
-/

namespace ComputableAnalysis

namespace FiniteRotationQuarterTurnExample

def quarterTurnInput : Rat := 355 / 226

def quarterTurnBox (n : Nat) : QBox :=
  RotationSeries.uniformRotationBox quarterTurnInput n

def unitImaginaryPoint : QBox :=
  QBox.point RotationSeries.imaginaryUnit

def quarterTurnTolerance : Rat := 1 / 100

def quarterTurnExpandedBox (n : Nat) : QBox :=
  QBox.expand (quarterTurnBox n) quarterTurnTolerance

theorem quarterTurnBox_contains_unit_imaginary_stage_eight :
    unitImaginaryPoint.NestedIn (quarterTurnExpandedBox 8) := by
  unfold unitImaginaryPoint quarterTurnExpandedBox quarterTurnBox
    quarterTurnTolerance QBox.NestedIn QBox.expand QBox.point
  simp only [QComplex.le_def]
  native_decide

theorem quarterTurnBox_contains_unit_imaginary_stage_twelve :
    unitImaginaryPoint.NestedIn (quarterTurnExpandedBox 12) := by
  unfold unitImaginaryPoint quarterTurnExpandedBox quarterTurnBox
    quarterTurnTolerance QBox.NestedIn QBox.expand QBox.point
  simp only [QComplex.le_def]
  native_decide

theorem quarterTurnBox_contains_unit_imaginary_stage_sixteen :
    unitImaginaryPoint.NestedIn (quarterTurnExpandedBox 16) := by
  unfold unitImaginaryPoint quarterTurnExpandedBox quarterTurnBox
    quarterTurnTolerance QBox.NestedIn QBox.expand QBox.point
  simp only [QComplex.le_def]
  native_decide

theorem quarterTurnBox_width_stage_sixteen :
    (quarterTurnBox 16).width =
      2 * RotationSeries.uniformRotationTailRadius 16 := by
  exact RotationSeries.uniformRotationBox_width quarterTurnInput 16

end FiniteRotationQuarterTurnExample

end ComputableAnalysis
