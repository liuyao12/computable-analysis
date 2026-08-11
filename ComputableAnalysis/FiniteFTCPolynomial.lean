import ComputableAnalysis.Series
import ComputableAnalysis.Calculus

/-!
# A finite cubic FTC certificate

The accumulator below is the left Riemann sum for `3 * x^2` on `[0,1]`,
written directly in finite rational data.  Its closed form and error budget
are useful without introducing a completed integral or a limiting real.
-/

namespace ComputableAnalysis

namespace FiniteFTC

def cubeDerivativeLeftSum (n : Nat) : Rat :=
  if n = 0 then 0
  else (3 : Rat) * Series.squareSum n / (n : Rat) ^ 3

/- The matching right-endpoint accumulator on the same rational partition. -/
def cubeDerivativeRightSum (n : Nat) : Rat :=
  if n = 0 then 0
  else (3 : Rat) * Series.squareSum (n + 1) / (n : Rat) ^ 3

theorem cubeDerivativeLeftSum_eq
    {n : Nat} (hn : 0 < n) :
    cubeDerivativeLeftSum n =
      ((n : Rat) - 1) * (2 * (n : Rat) - 1) /
        (2 * (n : Rat) ^ 2) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  unfold cubeDerivativeLeftSum
  simp [hn0, Series.squareSum_eq]
  rw [Rat.div_def]
  have hcast : (n : Rat) ≠ 0 := by
    exact Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.pow_succ, Rat.mul_inv_cancel]

theorem cubeDerivativeLeftSum_error_eq
    {n : Nat} (hn : 0 < n) :
    1 - cubeDerivativeLeftSum n =
      (3 * (n : Rat) - 1) / (2 * (n : Rat) ^ 2) := by
  rw [cubeDerivativeLeftSum_eq hn]
  rw [Rat.div_def]
  have hcast : (n : Rat) ≠ 0 := by
    exact Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.pow_succ, Rat.mul_inv_cancel]

theorem cubeDerivativeLeftSum_error_nonneg
    {n : Nat} (hn : 0 < n) :
    0 <= 1 - cubeDerivativeLeftSum n := by
  rw [cubeDerivativeLeftSum_error_eq hn, Rat.div_def]
  have hnrat : 0 < (n : Rat) := (Rat.natCast_pos).2 hn
  have hden : 0 < 2 * (n : Rat) ^ 2 := by
    exact Rat.mul_pos (by native_decide) (Rat.pow_pos hnrat)
  have hnum : 0 <= 3 * (n : Rat) - 1 := by
    have hnr : (1 : Rat) <= (n : Rat) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))
    grind
  exact Rat.mul_nonneg hnum (Rat.le_of_lt ((Rat.inv_pos).2 hden))

theorem cubeDerivativeLeftSum_error_le_three_halves_div
    {n : Nat} (hn : 0 < n) :
    1 - cubeDerivativeLeftSum n <= 3 / (2 * (n : Rat)) := by
  rw [cubeDerivativeLeftSum_error_eq hn]
  have hnrat : 0 < (n : Rat) := (Rat.natCast_pos).2 hn
  have hden : 0 < 2 * (n : Rat) ^ 2 := by
    exact Rat.mul_pos (by native_decide) (Rat.pow_pos hnrat)
  apply Rat.le_of_mul_le_mul_right (c := 2 * (n : Rat) ^ 2)
  · rw [Rat.div_def, Rat.div_def]
    have hne : (n : Rat) ≠ 0 := Rat.ne_of_gt hnrat
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
      Rat.pow_succ, Rat.mul_inv_cancel]
  · exact hden

theorem cubeDerivativeRightSum_eq
    {n : Nat} (hn : 0 < n) :
    cubeDerivativeRightSum n =
      ((n : Rat) + 1) * (2 * (n : Rat) + 1) /
        (2 * (n : Rat) ^ 2) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  unfold cubeDerivativeRightSum
  simp [hn0, Series.squareSum_eq]
  rw [Rat.div_def]
  have hcast : (n : Rat) ≠ 0 := by
    exact Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.pow_succ, Rat.mul_inv_cancel]

theorem cubeDerivativeRightSum_error_eq
    {n : Nat} (hn : 0 < n) :
    cubeDerivativeRightSum n - 1 =
      (3 * (n : Rat) + 1) / (2 * (n : Rat) ^ 2) := by
  rw [cubeDerivativeRightSum_eq hn]
  rw [Rat.div_def]
  have hcast : (n : Rat) ≠ 0 := by
    exact Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.pow_succ, Rat.mul_inv_cancel]

theorem cubeDerivativeRightSum_error_nonneg
    {n : Nat} (hn : 0 < n) :
    0 <= cubeDerivativeRightSum n - 1 := by
  rw [cubeDerivativeRightSum_error_eq hn, Rat.div_def]
  have hnrat : 0 < (n : Rat) := (Rat.natCast_pos).2 hn
  have hden : 0 < 2 * (n : Rat) ^ 2 := by
    exact Rat.mul_pos (by native_decide) (Rat.pow_pos hnrat)
  have hnum : 0 <= 3 * (n : Rat) + 1 := by grind
  exact Rat.mul_nonneg hnum (Rat.le_of_lt ((Rat.inv_pos).2 hden))

end FiniteFTC

end ComputableAnalysis
