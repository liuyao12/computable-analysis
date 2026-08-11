import ComputableAnalysis.ThreeByThreeLinearAlgebra

/-!
# Finite linear-algebra benchmark certificate

This module records a reusable `3 x 3` rational matrix-power recurrence.  It
is obtained by multiplying the project's explicit Cayley--Hamilton identity
by a finite natural-number power.  Thus every requested instance is a finite
matrix product and a rational arithmetic identity: no general determinant
library, completed field, or infinite process is used.
-/

namespace ComputableAnalysis

namespace LinearODE

open HarmonicOscillator

/-- The powers of an explicit rational `3 x 3` matrix satisfy the recurrence

`A^(n + 3) = tr(A) A^(n + 2) - s₂(A) A^(n + 1) + det(A) A^n`.

Here all coefficients are the nine-entry formulas from
`threeByThreeTrace`, `threeByThreeSecondCoeff`, and
`threeByThreeDeterminant`.  This is a finite rational certificate: `n` is a
natural stage and `matrixPow` is the project's recursive finite product. -/
theorem threeByThree_matrixPow_succ_succ_succ_recurrence
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    let A := threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22
    forall n,
      matrixPow A (n + 3) =
        matrixAdd
          (matrixScale (threeByThreeTrace a00 a01 a02 a10 a11 a12 a20 a21 a22)
            (matrixPow A (n + 2)))
          (matrixAdd
            (matrixScale
              (-(threeByThreeSecondCoeff a00 a01 a02 a10 a11 a12 a20 a21 a22))
              (matrixPow A (n + 1)))
            (matrixScale
              (threeByThreeDeterminant a00 a01 a02 a10 a11 a12 a20 a21 a22)
              (matrixPow A n))) := by
  dsimp
  let A := threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22
  let trace := threeByThreeTrace a00 a01 a02 a10 a11 a12 a20 a21 a22
  let second := threeByThreeSecondCoeff a00 a01 a02 a10 a11 a12 a20 a21 a22
  let determinant := threeByThreeDeterminant a00 a01 a02 a10 a11 a12 a20 a21 a22
  have hbase :
      matrixMul A (matrixMul A A) =
        matrixAdd
          (matrixScale trace (matrixMul A A))
          (matrixAdd
            (matrixScale (-second) A)
            (matrixScale determinant (matrixIdentity 3))) := by
    have hCH := threeByThree_cayley_hamilton
      a00 a01 a02 a10 a11 a12 a20 a21 a22
    change matrixAdd (matrixMul A (matrixMul A A))
        (matrixAdd (matrixScale (-trace) (matrixMul A A))
          (matrixAdd (matrixScale second A)
            (matrixScale (-determinant) (matrixIdentity 3)))) = matrixZero 3 at hCH
    funext i j
    have hij := congrFun (congrFun hCH i) j
    dsimp [matrixAdd, matrixScale, matrixZero] at hij ⊢
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  intro n
  rw [show n + 3 = 3 + n by omega, matrixPow_add A 3 n]
  change matrixMul (matrixMul A (matrixMul A (matrixMul A (matrixIdentity 3))))
      (matrixPow A n) = _
  rw [matrixMul_identity_right, hbase, matrixMul_add_left, matrixMul_add_left,
    matrixMul_matrixScale_left, matrixMul_matrixScale_left,
    matrixMul_matrixScale_left, matrixMul_identity_left]
  rw [show n + 2 = 2 + n by omega, matrixPow_add A 2 n]
  rw [show n + 1 = 1 + n by omega, matrixPow_add A 1 n]
  simp only [matrixPow, matrixMul_identity_right]
  rfl

end LinearODE

end ComputableAnalysis
