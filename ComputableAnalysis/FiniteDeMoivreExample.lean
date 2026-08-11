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

end Trigonometry

end RationalCircle

end ComputableAnalysis
