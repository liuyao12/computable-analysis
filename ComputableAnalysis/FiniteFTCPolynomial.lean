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

/-! A next finite endpoint-sum checkpoint for the derivative of `x^6`. -/

def sexticDerivativeLeftSum (n : Nat) : Rat :=
  if n = 0 then 0
  else (6 : Rat) * Series.fifthPowerSum n / (n : Rat) ^ 6

theorem sexticDerivativeLeftSum_stage8 :
    sexticDerivativeLeftSum 8 = (5439 : Rat) / 8192 := by
  native_decide

theorem sexticDerivativeLeftSum_stage8_le_integral_value :
    sexticDerivativeLeftSum 8 <= (6 : Rat) / 7 := by
  rw [sexticDerivativeLeftSum_stage8]
  native_decide

theorem sexticDerivativeLeftSum_stage16 :
    sexticDerivativeLeftSum 16 = (107775 : Rat) / 131072 := by
  native_decide

theorem sexticDerivativeLeftSum_stage16_le_integral_value :
    sexticDerivativeLeftSum 16 <= (6 : Rat) / 7 := by
  rw [sexticDerivativeLeftSum_stage16]
  native_decide

theorem sexticDerivativeLeftSum_stage32 :
    sexticDerivativeLeftSum 32 = (1905663 : Rat) / 2097152 := by
  native_decide

theorem sexticDerivativeLeftSum_stage32_le_one :
    sexticDerivativeLeftSum 32 <= (1 : Rat) := by
  rw [sexticDerivativeLeftSum_stage32]
  native_decide

theorem sexticDerivativeLeftSum_stage64 :
    sexticDerivativeLeftSum 64 = (32002047 : Rat) / 33554432 := by
  native_decide

theorem sexticDerivativeLeftSum_stage64_le_one :
    sexticDerivativeLeftSum 64 <= (1 : Rat) := by
  rw [sexticDerivativeLeftSum_stage64]
  native_decide

theorem sexticDerivativeLeftSum_stage128 :
    sexticDerivativeLeftSum 128 = (524369919 : Rat) / 536870912 := by
  native_decide

theorem sexticDerivativeLeftSum_stage128_le_one :
    sexticDerivativeLeftSum 128 <= (1 : Rat) := by
  rw [sexticDerivativeLeftSum_stage128]
  native_decide

theorem sexticDerivativeLeftSum_stage256 :
    sexticDerivativeLeftSum 256 = (8489598975 : Rat) / 8589934592 := by
  native_decide

theorem sexticDerivativeLeftSum_stage256_le_one :
    sexticDerivativeLeftSum 256 <= (1 : Rat) := by
  rw [sexticDerivativeLeftSum_stage256]
  native_decide

/-! The matching right-endpoint checkpoint for `6*x^5`.  At a fixed finite
stage, the two sums already form a certified Darboux enclosure of the
endpoint difference `1` for the primitive `x^6`; no limiting object is used. -/

def sexticDerivativeRightSum (n : Nat) : Rat :=
  if n = 0 then 0
  else (6 : Rat) * Series.fifthPowerSum (n + 1) / (n : Rat) ^ 6

theorem sexticDerivativeRightSum_stage8 :
    sexticDerivativeRightSum 8 = (11583 : Rat) / 8192 := by
  native_decide

theorem sexticDerivative_stage8_sandwich :
    sexticDerivativeLeftSum 8 <= (6 : Rat) / 7 /\
      (6 : Rat) / 7 <= sexticDerivativeRightSum 8 := by
  constructor
  · rw [sexticDerivativeLeftSum_stage8]
    native_decide
  · rw [sexticDerivativeRightSum_stage8]
    native_decide

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

/-! The two finite Darboux sums sandwich the endpoint difference for `x^3`.
This is the concrete computable FTC statement behind the derivative `3*x^2`;
the completed integral is represented here by the exact rational endpoint
difference `1`, not by a classical limit object. -/
theorem cubeDerivativeLeftSum_le_one_le_rightSum
    {n : Nat} (hn : 0 < n) :
    cubeDerivativeLeftSum n <= 1 /\
      1 <= cubeDerivativeRightSum n := by
  constructor
  · have herror := cubeDerivativeLeftSum_error_nonneg hn
    grind
  · have herror := cubeDerivativeRightSum_error_nonneg hn
    grind

theorem cubeDerivativeLeftSum_rightSum_gap_le_three_div
    {n : Nat} (hn : 0 < n) :
    cubeDerivativeRightSum n - cubeDerivativeLeftSum n <=
      3 / (n : Rat) := by
  rw [cubeDerivativeRightSum_eq hn, cubeDerivativeLeftSum_eq hn]
  have hnrat : 0 < (n : Rat) := (Rat.natCast_pos).2 hn
  have hne : (n : Rat) ≠ 0 := Rat.ne_of_gt hnrat
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.pow_succ, Rat.mul_inv_cancel]

end FiniteFTC

end ComputableAnalysis
