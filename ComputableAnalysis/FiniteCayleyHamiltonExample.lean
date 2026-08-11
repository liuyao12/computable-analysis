import ComputableAnalysis.PeanoBaker
import ComputableAnalysis.FiniteCayleyHamiltonBoundary

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

def concreteFourCayleyMatrix : RatMatrix 4 := fun i j =>
  if i = j then
    if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else 4
  else 0

def concreteFourCayleyCertificate :
    FiniteCayleyHamiltonCertificate 4 where
  matrix := concreteFourCayleyMatrix
  lowerCoefficients := [24, -50, 35, -10]
  annihilates := by
    apply funext
    intro i
    apply funext
    intro j
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl <;>
        native_decide

theorem concreteFourCayleyMatrix_annihilates :
    matrixPolynomialSum concreteFourCayleyMatrix
        ([24, -50, 35, -10] ++ [1]) 0 = matrixZero 4 := by
  exact concreteFourCayleyCertificate.annihilates

end LinearODE
end ComputableAnalysis
