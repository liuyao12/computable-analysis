import ComputableAnalysis.ComplexCircleBridge

/-!
# A finite De Moivre certificate

This file records one explicit power computation on the rational unit circle.
It is the algorithmic, rational-coordinate core of a low-degree De Moivre
identity: no angle parameter, completed complex number, or limiting process is
used.
-/

namespace ComputableAnalysis

namespace RationalCircle

namespace Trigonometry

def deMoivreThreeFive : PiCirclePoint :=
  { x := 3 / 5, y := 4 / 5 }

def deMoivreThreeFiveSquare : PiCirclePoint :=
  { x := -7 / 25, y := 24 / 25 }

def deMoivreThreeFiveCube : PiCirclePoint :=
  { x := -117 / 125, y := 44 / 125 }

def deMoivreThreeFiveFourth : PiCirclePoint :=
  { x := -527 / 625, y := -336 / 625 }

def deMoivreThreeFiveFifth : PiCirclePoint :=
  { x := -237 / 3125, y := -3116 / 3125 }

def deMoivreThreeFiveSixth : PiCirclePoint :=
  { x := 11753 / 15625, y := -10296 / 15625 }

theorem deMoivreThreeFive_unit :
    Stage.normSq deMoivreThreeFive = 1 := by
  native_decide

theorem deMoivreThreeFive_square :
    pointPow deMoivreThreeFive 2 = deMoivreThreeFiveSquare := by
  native_decide

theorem deMoivreThreeFive_square_coordinates :
    (pointPow deMoivreThreeFive 2).x = -7 / 25 ∧
      (pointPow deMoivreThreeFive 2).y = 24 / 25 := by
  rw [deMoivreThreeFive_square]
  constructor <;> rfl

theorem deMoivreThreeFive_square_unit :
    Stage.normSq (pointPow deMoivreThreeFive 2) = 1 := by
  exact pointPow_normSq_of_unit deMoivreThreeFive_unit 2

theorem deMoivreThreeFive_square_complex_bridge :
    toQComplex (pointPow deMoivreThreeFive 2) =
      QComplex.natPow (toQComplex deMoivreThreeFive) 2 := by
  exact toQComplex_pointPow deMoivreThreeFive 2

theorem deMoivreThreeFive_cube :
    pointPow deMoivreThreeFive 3 = deMoivreThreeFiveCube := by
  rw [pointPow_three]
  native_decide

theorem deMoivreThreeFive_cube_coordinates :
    (pointPow deMoivreThreeFive 3).x = -117 / 125 ∧
      (pointPow deMoivreThreeFive 3).y = 44 / 125 := by
  rw [deMoivreThreeFive_cube]
  constructor <;> rfl

theorem deMoivreThreeFive_cube_unit :
    Stage.normSq (pointPow deMoivreThreeFive 3) = 1 := by
  exact pointPow_normSq_of_unit deMoivreThreeFive_unit 3

theorem deMoivreThreeFive_fourth :
    pointPow deMoivreThreeFive 4 = deMoivreThreeFiveFourth := by
  rw [show 4 = 3 + 1 by omega, pointPow_succ]
  rw [deMoivreThreeFive_cube]
  native_decide

theorem deMoivreThreeFive_fourth_coordinates :
    (pointPow deMoivreThreeFive 4).x = -527 / 625 ∧
      (pointPow deMoivreThreeFive 4).y = -336 / 625 := by
  rw [deMoivreThreeFive_fourth]
  constructor <;> rfl

theorem deMoivreThreeFive_fourth_unit :
    Stage.normSq (pointPow deMoivreThreeFive 4) = 1 := by
  exact pointPow_normSq_of_unit deMoivreThreeFive_unit 4

theorem deMoivreThreeFive_fourth_complex_bridge :
    toQComplex (pointPow deMoivreThreeFive 4) =
      QComplex.natPow (toQComplex deMoivreThreeFive) 4 := by
  exact toQComplex_pointPow deMoivreThreeFive 4

theorem deMoivreThreeFive_fifth :
    pointPow deMoivreThreeFive 5 = deMoivreThreeFiveFifth := by
  rw [show 5 = 4 + 1 by omega, pointPow_succ]
  rw [deMoivreThreeFive_fourth]
  native_decide

theorem deMoivreThreeFive_fifth_coordinates :
    (pointPow deMoivreThreeFive 5).x = -237 / 3125 /\
      (pointPow deMoivreThreeFive 5).y = -3116 / 3125 := by
  rw [deMoivreThreeFive_fifth]
  constructor <;> rfl

theorem deMoivreThreeFive_fifth_unit :
    Stage.normSq (pointPow deMoivreThreeFive 5) = 1 := by
  exact pointPow_normSq_of_unit deMoivreThreeFive_unit 5

theorem deMoivreThreeFive_fifth_complex_bridge :
    toQComplex (pointPow deMoivreThreeFive 5) =
      QComplex.natPow (toQComplex deMoivreThreeFive) 5 := by
  exact toQComplex_pointPow deMoivreThreeFive 5

theorem deMoivreThreeFive_sixth :
    pointPow deMoivreThreeFive 6 = deMoivreThreeFiveSixth := by
  rw [show 6 = 5 + 1 by omega, pointPow_succ]
  rw [deMoivreThreeFive_fifth]
  native_decide

theorem deMoivreThreeFive_sixth_coordinates :
    (pointPow deMoivreThreeFive 6).x = 11753 / 15625 /\
      (pointPow deMoivreThreeFive 6).y = -10296 / 15625 := by
  rw [deMoivreThreeFive_sixth]
  constructor <;> rfl

theorem deMoivreThreeFive_sixth_unit :
    Stage.normSq (pointPow deMoivreThreeFive 6) = 1 := by
  exact pointPow_normSq_of_unit deMoivreThreeFive_unit 6

theorem deMoivreThreeFive_sixth_complex_bridge :
    toQComplex (pointPow deMoivreThreeFive 6) =
      QComplex.natPow (toQComplex deMoivreThreeFive) 6 := by
  exact toQComplex_pointPow deMoivreThreeFive 6

def deMoivreThreeFiveSeventh : PiCirclePoint :=
  { x := 76443 / 78125, y := 16124 / 78125 }

theorem deMoivreThreeFive_seventh :
    pointPow deMoivreThreeFive 7 = deMoivreThreeFiveSeventh := by
  rw [show 7 = 6 + 1 by omega, pointPow_succ]
  rw [deMoivreThreeFive_sixth]
  native_decide

theorem deMoivreThreeFive_seventh_coordinates :
    (pointPow deMoivreThreeFive 7).x = 76443 / 78125 /\
      (pointPow deMoivreThreeFive 7).y = 16124 / 78125 := by
  rw [deMoivreThreeFive_seventh]
  constructor <;> rfl

theorem deMoivreThreeFive_seventh_unit :
    Stage.normSq (pointPow deMoivreThreeFive 7) = 1 := by
  exact pointPow_normSq_of_unit deMoivreThreeFive_unit 7

theorem deMoivreThreeFive_seventh_complex_bridge :
    toQComplex (pointPow deMoivreThreeFive 7) =
      QComplex.natPow (toQComplex deMoivreThreeFive) 7 := by
  exact toQComplex_pointPow deMoivreThreeFive 7

end Trigonometry

end RationalCircle

end ComputableAnalysis
