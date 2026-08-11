import ComputableAnalysis.ThreeByThreeLinearAlgebra

/-!
# A finite arbitrary-matrix bridge for `3 x 3` Cayley--Hamilton

The explicit `3 x 3` certificate in `PeanoBaker` is stated using nine named
rational entries.  This file supplies the finite extensionality bridge back
to arbitrary rational matrix data.  No ambient determinant or completeness
principle is used: all coefficients are read from the nine matrix entries.
-/

namespace ComputableAnalysis

namespace LinearODE

namespace HarmonicOscillator

/-- The trace read directly from an arbitrary rational `3 x 3` matrix. -/
def ratMatrixThreeTrace (A : RatMatrix 3) : Rat := A 0 0 + A 1 1 + A 2 2

/-- The second characteristic coefficient read from an arbitrary rational
`3 x 3` matrix. -/
def ratMatrixThreeSecondCoeff (A : RatMatrix 3) : Rat :=
  A 0 0 * A 1 1 + A 0 0 * A 2 2 + A 1 1 * A 2 2 -
    A 0 1 * A 1 0 - A 0 2 * A 2 0 - A 1 2 * A 2 1

/-- The finite determinant formula read directly from an arbitrary rational
`3 x 3` matrix. -/
def ratMatrixThreeDeterminant (A : RatMatrix 3) : Rat :=
  A 0 0 * (A 1 1 * A 2 2 - A 1 2 * A 2 1) -
    A 0 1 * (A 1 0 * A 2 2 - A 1 2 * A 2 0) +
    A 0 2 * (A 1 0 * A 2 1 - A 1 1 * A 2 0)

/-- Every rational `3 x 3` matrix is extensionally its nine-entry explicit
presentation. -/
theorem ratMatrix_threeByThree_eq_explicit (A : RatMatrix 3) :
    A = threeByThreeMatrix
      (A 0 0) (A 0 1) (A 0 2)
      (A 1 0) (A 1 1) (A 1 2)
      (A 2 0) (A 2 1) (A 2 2) := by
  funext i j
  have hi : i = 0 \/ i = 1 \/ i = 2 := by omega
  have hj : j = 0 \/ j = 1 \/ j = 2 := by omega
  rcases hi with rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl <;> rfl

/-- Generic finite rational `3 x 3` Cayley--Hamilton identity, transported
from the explicit nine-entry certificate. -/
theorem ratMatrix_threeByThree_cayley_hamilton (A : RatMatrix 3) :
    matrixAdd (matrixMul A (matrixMul A A))
        (matrixAdd
          (matrixScale (-(ratMatrixThreeTrace A)) (matrixMul A A))
          (matrixAdd
            (matrixScale (ratMatrixThreeSecondCoeff A) A)
            (matrixScale (-(ratMatrixThreeDeterminant A))
              (matrixIdentity 3)))) =
      matrixZero 3 := by
  have hA := ratMatrix_threeByThree_eq_explicit A
  rw [hA]
  simpa [ratMatrixThreeTrace, ratMatrixThreeSecondCoeff,
    ratMatrixThreeDeterminant, threeByThreeTrace, threeByThreeSecondCoeff,
    threeByThreeDeterminant, threeByThreeMatrix_00, threeByThreeMatrix_01,
    threeByThreeMatrix_02, threeByThreeMatrix_10,
    threeByThreeMatrix_11, threeByThreeMatrix_12,
    threeByThreeMatrix_20, threeByThreeMatrix_21,
    threeByThreeMatrix_22] using
    (threeByThree_cayley_hamilton
      (A 0 0) (A 0 1) (A 0 2)
      (A 1 0) (A 1 1) (A 1 2)
      (A 2 0) (A 2 1) (A 2 2))

/-- Every finite power of an arbitrary rational `3 x 3` matrix satisfies the
third-order recurrence induced by its supplied characteristic coefficients. -/
theorem ratMatrix_threeByThree_matrixPow_recurrence (A : RatMatrix 3) :
    ∀ n,
      matrixPow A (n + 3) =
        matrixAdd
          (matrixScale (ratMatrixThreeTrace A) (matrixPow A (n + 2)))
          (matrixAdd
            (matrixScale (-(ratMatrixThreeSecondCoeff A))
              (matrixPow A (n + 1)))
            (matrixScale (ratMatrixThreeDeterminant A) (matrixPow A n))) := by
  have hbase :
      matrixMul A (matrixMul A A) =
        matrixAdd
          (matrixScale (ratMatrixThreeTrace A) (matrixMul A A))
          (matrixAdd
            (matrixScale (-(ratMatrixThreeSecondCoeff A)) A)
            (matrixScale (ratMatrixThreeDeterminant A)
              (matrixIdentity 3))) := by
    have hCH := ratMatrix_threeByThree_cayley_hamilton A
    funext i j
    have hij := congrFun (congrFun hCH i) j
    dsimp [matrixAdd, matrixScale, matrixZero] at hij ⊢
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  intro n
  rw [show n + 3 = 3 + n by omega, matrixPow_add A 3 n]
  change matrixMul
      (matrixMul A (matrixMul A (matrixMul A (matrixIdentity 3))))
      (matrixPow A n) = _
  rw [matrixMul_identity_right, hbase, matrixMul_add_left,
    matrixMul_add_left, matrixMul_matrixScale_left,
    matrixMul_matrixScale_left, matrixMul_matrixScale_left,
    matrixMul_identity_left]
  rw [show n + 2 = 2 + n by omega, matrixPow_add A 2 n]
  rw [show n + 1 = 1 + n by omega, matrixPow_add A 1 n]
  simp only [matrixPow, matrixMul_identity_right]

end HarmonicOscillator

end LinearODE

end ComputableAnalysis
