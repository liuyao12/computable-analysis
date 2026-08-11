import ComputableAnalysis.PeanoBaker

namespace ComputableAnalysis
namespace LinearODE

open HarmonicOscillator

/-! A concrete rational Cayley--Hamilton certificate for item 49. -/

def concreteCayleyMatrix : RatMatrix 2 := twoByTwoMatrix 1 2 0 3

theorem concreteCayleyMatrix_trace :
    twoByTwoTrace 1 2 0 3 = 4 := by
  native_decide

theorem concreteCayleyMatrix_determinant :
    twoByTwoDeterminant 1 2 0 3 = 3 := by
  native_decide

theorem concreteCayleyMatrix_identity :
    matrixAdd (matrixMul concreteCayleyMatrix concreteCayleyMatrix)
        (matrixAdd
          (matrixScale (-4) concreteCayleyMatrix)
          (matrixScale 3 (matrixIdentity 2))) =
      matrixZero 2 := by
  simpa [concreteCayleyMatrix, concreteCayleyMatrix_trace,
    concreteCayleyMatrix_determinant] using
    (HarmonicOscillator.twoByTwo_cayley_hamilton 1 2 0 3)

theorem concreteCayleyMatrix_identity_from_generic :
    matrixAdd (matrixMul concreteCayleyMatrix concreteCayleyMatrix)
        (matrixAdd
          (matrixScale (-(twoByTwoTrace 1 2 0 3)) concreteCayleyMatrix)
          (matrixScale (twoByTwoDeterminant 1 2 0 3) (matrixIdentity 2))) =
      matrixZero 2 := by
  simpa [concreteCayleyMatrix, concreteCayleyMatrix_trace,
    concreteCayleyMatrix_determinant] using
    (HarmonicOscillator.twoByTwo_cayley_hamilton 1 2 0 3)

end LinearODE
end ComputableAnalysis
