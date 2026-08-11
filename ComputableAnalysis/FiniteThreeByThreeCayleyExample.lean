import ComputableAnalysis.PeanoBaker

/-!
# A worked finite 3x3 Cayley--Hamilton certificate

The diagonal rational matrix `diag(1,2,3)` has characteristic coefficients
`6`, `11`, and `6`.  The certificate checks the explicit identity
`A^3 - 6 A^2 + 11 A - 6 I = 0` through the project's finite matrix layer.
-/

namespace ComputableAnalysis

namespace LinearODE

open HarmonicOscillator

def concreteThreeCayleyMatrix : RatMatrix 3 :=
  threeByThreeMatrix 1 0 0 0 2 0 0 0 3

theorem concreteThreeCayleyMatrix_trace :
    threeByThreeTrace 1 0 0 0 2 0 0 0 3 = 6 := by
  native_decide

theorem concreteThreeCayleyMatrix_secondCoeff :
    threeByThreeSecondCoeff 1 0 0 0 2 0 0 0 3 = 11 := by
  native_decide

theorem concreteThreeCayleyMatrix_determinant :
    threeByThreeDeterminant 1 0 0 0 2 0 0 0 3 = 6 := by
  native_decide

theorem concreteThreeCayleyMatrix_identity :
    matrixAdd (matrixMul concreteThreeCayleyMatrix
        (matrixMul concreteThreeCayleyMatrix concreteThreeCayleyMatrix))
        (matrixAdd
          (matrixScale (-6) (matrixMul concreteThreeCayleyMatrix
            concreteThreeCayleyMatrix))
          (matrixAdd
            (matrixScale 11 concreteThreeCayleyMatrix)
            (matrixScale (-6) (matrixIdentity 3)))) =
      matrixZero 3 := by
  simpa [concreteThreeCayleyMatrix, concreteThreeCayleyMatrix_trace,
    concreteThreeCayleyMatrix_secondCoeff,
    concreteThreeCayleyMatrix_determinant] using
    (HarmonicOscillator.threeByThree_cayley_hamilton
      1 0 0 0 2 0 0 0 3)

end LinearODE

end ComputableAnalysis
