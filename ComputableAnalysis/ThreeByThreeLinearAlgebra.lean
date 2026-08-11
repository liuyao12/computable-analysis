import ComputableAnalysis.PeanoBaker

/-!
# Finite `3 x 3` rational linear algebra

This module extends the local matrix layer with an explicit rational Cramer
solver.  The inverse determinant is supplied as a rational certificate; no
general determinant library or completed field is introduced.
-/

namespace ComputableAnalysis

namespace LinearODE

open HarmonicOscillator

private theorem finiteSum_three_cramer (f : Fin 3 -> Rat) :
    finiteSum f = f 0 + f 1 + f 2 := by
  change f 0 + (f 1 + (f 2 + 0)) = f 0 + f 1 + f 2
  grind [Rat.add_assoc]

def threeVector (u v w : Rat) : RatVector 3 :=
  fun i => Fin.cases u (fun i => Fin.cases v (fun i => Fin.cases w (fun i => Fin.elim0 i) i) i) i

@[simp] theorem threeVector_zero (u v w : Rat) : threeVector u v w 0 = u := by rfl
@[simp] theorem threeVector_one (u v w : Rat) : threeVector u v w 1 = v := by rfl
@[simp] theorem threeVector_two (u v w : Rat) : threeVector u v w 2 = w := by rfl

theorem apply_threeByThree_explicit
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 u v w : Rat) :
    matrixApply (threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22)
      (threeVector u v w) =
      threeVector
        (a00 * u + a01 * v + a02 * w)
        (a10 * u + a11 * v + a12 * w)
        (a20 * u + a21 * v + a22 * w) := by
  funext i
  have hi : i = 0 \/ i = 1 \/ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;>
    simp [matrixApply, threeByThreeMatrix_00, threeByThreeMatrix_01,
      threeByThreeMatrix_02, threeByThreeMatrix_10,
      threeByThreeMatrix_11, threeByThreeMatrix_12,
      threeByThreeMatrix_20, threeByThreeMatrix_21,
      threeByThreeMatrix_22, finiteSum_three_cramer,
      threeVector_zero, threeVector_one, threeVector_two]

theorem threeByThree_cramer_row_expansions
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 x y z : Rat) :
    (a00 * threeByThreeDeterminant x a01 a02 y a11 a12 z a21 a22 +
        a01 * threeByThreeDeterminant a00 x a02 a10 y a12 a20 z a22 +
        a02 * threeByThreeDeterminant a00 a01 x a10 a11 y a20 a21 z =
      x * threeByThreeDeterminant a00 a01 a02 a10 a11 a12 a20 a21 a22) /\
    (a10 * threeByThreeDeterminant x a01 a02 y a11 a12 z a21 a22 +
        a11 * threeByThreeDeterminant a00 x a02 a10 y a12 a20 z a22 +
        a12 * threeByThreeDeterminant a00 a01 x a10 a11 y a20 a21 z =
      y * threeByThreeDeterminant a00 a01 a02 a10 a11 a12 a20 a21 a22) /\
    (a20 * threeByThreeDeterminant x a01 a02 y a11 a12 z a21 a22 +
        a21 * threeByThreeDeterminant a00 x a02 a10 y a12 a20 z a22 +
        a22 * threeByThreeDeterminant a00 a01 x a10 a11 y a20 a21 z =
      z * threeByThreeDeterminant a00 a01 a02 a10 a11 a12 a20 a21 a22) := by
  constructor
  · unfold threeByThreeDeterminant
    grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
      Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
  constructor
  · unfold threeByThreeDeterminant
    grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
      Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
  · unfold threeByThreeDeterminant
    grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
      Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

def threeByThreeCramerSolution
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 x y z dinv : Rat) : RatVector 3 :=
  threeVector
    (threeByThreeDeterminant x a01 a02 y a11 a12 z a21 a22 * dinv)
    (threeByThreeDeterminant a00 x a02 a10 y a12 a20 z a22 * dinv)
    (threeByThreeDeterminant a00 a01 x a10 a11 y a20 a21 z * dinv)

/-- Cramer's rule for an explicit rational `3 x 3` system, with the inverse
of the determinant supplied as finite rational data. -/
theorem threeByThree_cramer_solves
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 x y z dinv : Rat)
    (hdetinv : threeByThreeDeterminant a00 a01 a02 a10 a11 a12 a20 a21 a22 * dinv = 1) :
    matrixApply (threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22)
      (threeByThreeCramerSolution a00 a01 a02 a10 a11 a12 a20 a21 a22 x y z dinv) =
      threeVector x y z := by
  have hrows := threeByThree_cramer_row_expansions
    a00 a01 a02 a10 a11 a12 a20 a21 a22 x y z
  have hrow0 := hrows.1
  have hrow1 := hrows.2.1
  have hrow2 := hrows.2.2
  change matrixApply (threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22)
      (threeVector
        (threeByThreeDeterminant x a01 a02 y a11 a12 z a21 a22 * dinv)
        (threeByThreeDeterminant a00 x a02 a10 y a12 a20 z a22 * dinv)
        (threeByThreeDeterminant a00 a01 x a10 a11 y a20 a21 z * dinv)) =
      threeVector x y z
  rw [apply_threeByThree_explicit]
  funext i
  have hi : i = 0 \/ i = 1 \/ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · simp [threeByThreeCramerSolution]
    calc
      a00 * (threeByThreeDeterminant x a01 a02 y a11 a12 z a21 a22 * dinv) +
          a01 * (threeByThreeDeterminant a00 x a02 a10 y a12 a20 z a22 * dinv) +
          a02 * (threeByThreeDeterminant a00 a01 x a10 a11 y a20 a21 z * dinv) =
        (a00 * threeByThreeDeterminant x a01 a02 y a11 a12 z a21 a22 +
          a01 * threeByThreeDeterminant a00 x a02 a10 y a12 a20 z a22 +
          a02 * threeByThreeDeterminant a00 a01 x a10 a11 y a20 a21 z) * dinv := by
            grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc]
      _ = x := by rw [hrow0, Rat.mul_assoc, hdetinv]; grind
  · simp [threeByThreeCramerSolution]
    calc
      a10 * (threeByThreeDeterminant x a01 a02 y a11 a12 z a21 a22 * dinv) +
          a11 * (threeByThreeDeterminant a00 x a02 a10 y a12 a20 z a22 * dinv) +
          a12 * (threeByThreeDeterminant a00 a01 x a10 a11 y a20 a21 z * dinv) =
        (a10 * threeByThreeDeterminant x a01 a02 y a11 a12 z a21 a22 +
          a11 * threeByThreeDeterminant a00 x a02 a10 y a12 a20 z a22 +
          a12 * threeByThreeDeterminant a00 a01 x a10 a11 y a20 a21 z) * dinv := by
            grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc]
      _ = y := by rw [hrow1, Rat.mul_assoc, hdetinv]; grind
  · simp [threeByThreeCramerSolution]
    calc
      a20 * (threeByThreeDeterminant x a01 a02 y a11 a12 z a21 a22 * dinv) +
          a21 * (threeByThreeDeterminant a00 x a02 a10 y a12 a20 z a22 * dinv) +
          a22 * (threeByThreeDeterminant a00 a01 x a10 a11 y a20 a21 z * dinv) =
        (a20 * threeByThreeDeterminant x a01 a02 y a11 a12 z a21 a22 +
          a21 * threeByThreeDeterminant a00 x a02 a10 y a12 a20 z a22 +
          a22 * threeByThreeDeterminant a00 a01 x a10 a11 y a20 a21 z) * dinv := by
            grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc]
      _ = z := by rw [hrow2, Rat.mul_assoc, hdetinv]; grind

/-- The usual nonzero-determinant form: the rational inverse witness is the
canonical reciprocal of the determinant. -/
theorem threeByThree_cramer_solves_of_determinant_ne_zero
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 x y z : Rat)
    (hdet : threeByThreeDeterminant a00 a01 a02 a10 a11 a12 a20 a21 a22 ≠ 0) :
    matrixApply (threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22)
      (threeByThreeCramerSolution
        a00 a01 a02 a10 a11 a12 a20 a21 a22 x y z
        (threeByThreeDeterminant a00 a01 a02 a10 a11 a12 a20 a21 a22)⁻¹) =
      threeVector x y z := by
  apply threeByThree_cramer_solves
  exact Rat.mul_inv_cancel _ hdet

end LinearODE

end ComputableAnalysis
