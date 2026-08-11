import ComputableAnalysis.ThreeByThreeLinearAlgebra

/-!
# A worked finite 3x3 Cramer's-rule certificate

For the diagonal system `diag(2,3,4) u = (4,9,16)`, the determinant is `24`
and Cramer's formulas return `(2,3,4)` exactly.
-/

namespace ComputableAnalysis

namespace LinearODE

open HarmonicOscillator

def concreteThreeCramerSolution : RatVector 3 :=
  threeByThreeCramerSolution 2 0 0 0 3 0 0 0 4 4 9 16 (1 / 24)

theorem concreteThreeCramer_determinant :
    threeByThreeDeterminant 2 0 0 0 3 0 0 0 4 = 24 := by
  native_decide

theorem concreteThreeCramer_inverse_witness :
    threeByThreeDeterminant 2 0 0 0 3 0 0 0 4 * (1 / 24) = 1 := by
  native_decide

theorem concreteThreeCramer_solution :
    concreteThreeCramerSolution = threeVector 2 3 4 := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;>
    native_decide

theorem concreteThreeCramer_solves :
    matrixApply (threeByThreeMatrix 2 0 0 0 3 0 0 0 4)
        concreteThreeCramerSolution = threeVector 4 9 16 := by
  rw [concreteThreeCramer_solution]
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;>
    native_decide

theorem concreteThreeCramer_solves_from_generic :
    matrixApply (threeByThreeMatrix 2 0 0 0 3 0 0 0 4)
        (threeByThreeCramerSolution 2 0 0 0 3 0 0 0 4 4 9 16 (1 / 24)) =
      threeVector 4 9 16 := by
  apply threeByThree_cramer_solves
  exact concreteThreeCramer_inverse_witness

def concreteThreeNonDiagonalCramerSolution : RatVector 3 :=
  threeByThreeCramerSolution 2 1 0 0 3 1 1 0 2 4 9 7 (1 / 13)

theorem concreteThreeNonDiagonalCramer_determinant :
    threeByThreeDeterminant 2 1 0 0 3 1 1 0 2 = 13 := by
  native_decide

theorem concreteThreeNonDiagonalCramer_inverse_witness :
    threeByThreeDeterminant 2 1 0 0 3 1 1 0 2 * (1 / 13) = 1 := by
  native_decide

theorem concreteThreeNonDiagonalCramer_solution :
    concreteThreeNonDiagonalCramerSolution = threeVector 1 2 3 := by
  funext i
  have hi : i = 0 \/ i = 1 \/ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;>
    native_decide

theorem concreteThreeNonDiagonalCramer_solves :
    matrixApply (threeByThreeMatrix 2 1 0 0 3 1 1 0 2)
        concreteThreeNonDiagonalCramerSolution = threeVector 4 9 7 := by
  rw [concreteThreeNonDiagonalCramer_solution]
  funext i
  have hi : i = 0 \/ i = 1 \/ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;>
    native_decide

theorem concreteThreeNonDiagonalCramer_solves_from_generic :
    matrixApply (threeByThreeMatrix 2 1 0 0 3 1 1 0 2)
        (threeByThreeCramerSolution 2 1 0 0 3 1 1 0 2 4 9 7 (1 / 13)) =
      threeVector 4 9 7 := by
  apply threeByThree_cramer_solves
  exact concreteThreeNonDiagonalCramer_inverse_witness

end LinearODE

end ComputableAnalysis
