import ComputableAnalysis.Differential

/-!
# A finite rational L'Hôpital certificate

This module packages one useful step beyond bare common-factor cancellation.
After cancelling a nonzero linear factor, affine residuals admit an exact
cross-product remainder formula.  The formula records the coefficient that
controls the residual quotient algebraically; it is a finite rational
certificate and does not assert a limit theorem.
-/

namespace ComputableAnalysis

namespace FiniteLHopitalCertificate

/-- The affine residual left after a common linear factor is removed. -/
def affineResidual (c slope t : Rat) : Rat := c + slope * t

/-- Data for a quotient whose numerator and denominator share a nonzero
linear factor.  The denominator residual is required to be nonzero both at
the base point and at the displayed rational sample. -/
structure Certificate where
  step : Rat
  numConst : Rat
  numSlope : Rat
  denConst : Rat
  denSlope : Rat
  step_ne : step ≠ 0
  denConst_ne : denConst ≠ 0
  denominatorSample_ne :
    affineResidual denConst denSlope step ≠ 0

namespace Certificate

theorem common_factor_cancel (C : Certificate) :
    (C.step * affineResidual C.numConst C.numSlope C.step) /
        (C.step * affineResidual C.denConst C.denSlope C.step) =
      affineResidual C.numConst C.numSlope C.step /
        affineResidual C.denConst C.denSlope C.step := by
  have hstep : C.step - 0 ≠ 0 := by
    intro hz
    apply C.step_ne
    grind
  have hcancel := ExactFunction.common_linear_factor_quotient_cancel
    (a := 0) (x := C.step)
    (g := affineResidual C.numConst C.numSlope)
    (h := affineResidual C.denConst C.denSlope)
    hstep C.denominatorSample_ne
  rw [show C.step - 0 = C.step by grind] at hcancel
  exact hcancel

/-- Exact finite remainder after cancellation.  The numerator
`numeratorSlope * denominatorConstant - numeratorConstant * denominatorSlope`
is the cross-product certificate for the residual quotient. -/
theorem residual_remainder_identity (C : Certificate) :
    affineResidual C.numConst C.numSlope C.step /
        affineResidual C.denConst C.denSlope C.step -
      C.numConst / C.denConst =
      ((C.numSlope * C.denConst - C.numConst * C.denSlope) * C.step) /
        (C.denConst * affineResidual C.denConst C.denSlope C.step) := by
  unfold affineResidual
  rw [Rat.div_def, Rat.div_def]
  have hden :
      C.denConst * (C.denConst + C.denSlope * C.step) ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · exact C.denConst_ne hzero
    · exact C.denominatorSample_ne hzero
  have hsample :
      C.denConst + C.denSlope * C.step ≠ 0 :=
    C.denominatorSample_ne
  have hbase : C.denConst ≠ 0 := C.denConst_ne
  have hcancelBase : C.denConst * C.denConst⁻¹ = 1 :=
    Rat.mul_inv_cancel C.denConst hbase
  have hcancelSample :
      (C.denConst + C.denSlope * C.step) *
          (C.denConst + C.denSlope * C.step)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hsample
  have hcancelProduct :
      (C.denConst * (C.denConst + C.denSlope * C.step)) *
          (C.denConst * (C.denConst + C.denSlope * C.step))⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hden
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
    Rat.add_assoc, Rat.add_comm, Rat.mul_comm]

end Certificate

/-- A direct finite quotient-cancellation certificate with an explicit
cross-product remainder.  This is the public constructor for the common
linear-factor/affine-residual pattern. -/
theorem affine_residual_quotient_certificate
    (step numeratorConstant numeratorSlope denominatorConstant denominatorSlope : Rat)
    (hstep : step ≠ 0) (hden0 : denominatorConstant ≠ 0)
    (hden : denominatorConstant + denominatorSlope * step ≠ 0) :
    ((step * affineResidual numeratorConstant numeratorSlope step) /
        (step * affineResidual denominatorConstant denominatorSlope step)) -
      numeratorConstant / denominatorConstant =
      ((numeratorSlope * denominatorConstant - numeratorConstant * denominatorSlope) *
          step) /
        (denominatorConstant * affineResidual denominatorConstant denominatorSlope step) := by
  let C : Certificate :=
    { step := step
      numConst := numeratorConstant
      numSlope := numeratorSlope
      denConst := denominatorConstant
      denSlope := denominatorSlope
      step_ne := hstep
      denConst_ne := hden0
      denominatorSample_ne := hden }
  rw [Certificate.common_factor_cancel C]
  exact Certificate.residual_remainder_identity C

/-- When the two affine residuals have zero cross-product, the finite
quotient already has its base-point value exactly; no limiting argument is
needed. -/
theorem affine_residual_quotient_eq_base_of_cross_product_eq_zero
    (step numeratorConstant numeratorSlope denominatorConstant denominatorSlope : Rat)
    (hstep : step ≠ 0) (hden0 : denominatorConstant ≠ 0)
    (hden : denominatorConstant + denominatorSlope * step ≠ 0)
    (hcross : numeratorSlope * denominatorConstant -
      numeratorConstant * denominatorSlope = 0) :
    (step * affineResidual numeratorConstant numeratorSlope step) /
        (step * affineResidual denominatorConstant denominatorSlope step) =
      numeratorConstant / denominatorConstant := by
  have hidentity := affine_residual_quotient_certificate
    step numeratorConstant numeratorSlope denominatorConstant denominatorSlope
    hstep hden0 hden
  have hzero :
      (step * affineResidual numeratorConstant numeratorSlope step) /
          (step * affineResidual denominatorConstant denominatorSlope step) -
        numeratorConstant / denominatorConstant = 0 := by
    simpa [hcross, Rat.div_def] using hidentity
  grind [Rat.sub_eq_add_neg]

/-! A worked finite analogue of the usual `(x^2 - 1)/(x - 1)` example.
The common factor is represented by `step`; the residual quotient is `2 + step`,
so the exact error from the base value `2` is the computable quantity `step`.
-/

theorem quadratic_linear_worked_remainder (step : Rat) (hstep : step ≠ 0) :
    (step * affineResidual 2 1 step) /
        (step * affineResidual 1 0 step) - 2 = step := by
  have h := affine_residual_quotient_certificate
    step 2 1 1 0 hstep (by native_decide) (by
      rw [show (1 : Rat) + 0 * step = 1 by
        rw [Rat.zero_mul]
        native_decide]
      simp
      )
  have hcancel : step * step⁻¹ = 1 := Rat.mul_inv_cancel _ hstep
  simp only [affineResidual, Rat.zero_mul, Rat.add_zero, Rat.mul_one] at h ⊢
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

theorem quadratic_linear_worked_remainder_at_stage {n : Nat} (hn : 0 < n) :
    (1 / (n : Rat) * affineResidual 2 1 (1 / (n : Rat))) /
        (1 / (n : Rat) * affineResidual 1 0 (1 / (n : Rat))) - 2 =
      1 / (n : Rat) := by
  apply quadratic_linear_worked_remainder
  rw [Rat.div_def]
  exact Rat.ne_of_gt (Rat.mul_pos (by native_decide)
    ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hn)))

/-! A cubic analogue: after cancelling `(x-1)` from `x^3-1`, the residual
quotient at `x=1+step` differs from its base value `3` by `3*step+step^2`.
-/

theorem cubic_linear_worked_remainder (step : Rat) (hstep : step ≠ 0) :
    (step * (3 + 3 * step + step ^ 2)) / (step * 1) - 3 =
      3 * step + step ^ 2 := by
  have hcancel : step * step⁻¹ = 1 := Rat.mul_inv_cancel _ hstep
  rw [Rat.div_def]
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem cubic_linear_worked_remainder_at_stage {n : Nat} (hn : 0 < n) :
    ((1 / (n : Rat)) * (3 + 3 * (1 / (n : Rat)) +
        (1 / (n : Rat)) ^ 2)) /
        ((1 / (n : Rat)) * 1) - 3 =
      3 / (n : Rat) + (1 / (n : Rat)) ^ 2 := by
  have hstep : (1 / (n : Rat)) ≠ 0 := by
    rw [Rat.div_def]
    exact Rat.ne_of_gt (Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hn)))
  have h := cubic_linear_worked_remainder (1 / (n : Rat)) hstep
  simpa [Rat.div_def, Rat.mul_assoc, Rat.mul_comm] using h

/-! The stage formula also carries an explicit rational error budget. -/

set_option maxHeartbeats 10000000 in
theorem cubic_linear_worked_remainder_at_stage_error_le_four_div
    {n : Nat} (hn : 0 < n) :
    qabs (((1 / (n : Rat)) * (3 + 3 * (1 / (n : Rat)) +
        (1 / (n : Rat)) ^ 2)) /
        ((1 / (n : Rat)) * 1) - 3) <=
      4 / (n : Rat) := by
  have hstage := cubic_linear_worked_remainder_at_stage hn
  rw [hstage]
  let x : Rat := 1 / (n : Rat)
  have hxpos : 0 < x := by
    dsimp [x]
    rw [Rat.div_def]
    exact Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hn))
  have hxle : x <= 1 := by
    dsimp [x]
    rw [Rat.div_def]
    apply Rat.le_of_mul_le_mul_right (c := (n : Rat))
    · have hne : (n : Rat) ≠ 0 := Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
      have hinv : (n : Rat)⁻¹ * n = 1 := by
        rw [Rat.mul_comm]
        exact Rat.mul_inv_cancel _ hne
      simp only [Rat.one_mul]
      rw [hinv]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))
    · exact (Rat.natCast_pos).2 hn
  have hsq : x * x <= x := by
    have h := Rat.mul_le_mul_of_nonneg_left hxle (Rat.le_of_lt hxpos)
    simpa [Rat.mul_one] using h
  have hnonneg : 0 <= 3 * x + x ^ 2 := by
    exact Rat.add_nonneg
      (Rat.mul_nonneg (by native_decide) (Rat.le_of_lt hxpos))
      (Rat.pow_nonneg (Rat.le_of_lt hxpos))
  change qabs (3 * x + x ^ 2) <= 4 / (n : Rat)
  rw [qabs_eq_self_of_nonneg hnonneg]
  have hbound : 3 * x + x ^ 2 <= 4 * x := by
    rw [show x ^ 2 = x * x by
      simp [Rat.pow_succ, Rat.pow_zero, Rat.mul_assoc]]
    grind
  have hnrat : (0 : Rat) < n := (Rat.natCast_pos).2 hn
  have hfour : (4 : Rat) * x = 4 / (n : Rat) := by
    simp [x, Rat.div_def, Rat.mul_assoc]
  rw [← hfour]
  exact hbound

/-! The quartic analogue: after cancelling `(x-1)` from `x^4-1`, the
residual quotient differs from its base value `4` by the displayed finite
polynomial in the step. -/

theorem quartic_linear_worked_remainder (step : Rat) (hstep : step ≠ 0) :
    (step * (4 + 6 * step + 4 * step ^ 2 + step ^ 3)) / (step * 1) - 4 =
      6 * step + 4 * step ^ 2 + step ^ 3 := by
  have hcancel : step * step⁻¹ = 1 := Rat.mul_inv_cancel _ hstep
  rw [Rat.div_def]
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem quartic_linear_worked_remainder_at_stage {n : Nat} (hn : 0 < n) :
    ((1 / (n : Rat)) * (4 + 6 * (1 / (n : Rat)) +
        4 * (1 / (n : Rat)) ^ 2 + (1 / (n : Rat)) ^ 3)) /
        ((1 / (n : Rat)) * 1) - 4 =
      6 / (n : Rat) + 4 * (1 / (n : Rat)) ^ 2 +
        (1 / (n : Rat)) ^ 3 := by
  have hstep : (1 / (n : Rat)) ≠ 0 := by
    rw [Rat.div_def]
    exact Rat.ne_of_gt (Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hn)))
  have h := quartic_linear_worked_remainder (1 / (n : Rat)) hstep
  simpa [Rat.div_def, Rat.mul_assoc, Rat.mul_comm] using h

set_option maxHeartbeats 10000000 in
theorem quartic_linear_worked_remainder_at_stage_error_le_eleven_div
    {n : Nat} (hn : 0 < n) :
    qabs (((1 / (n : Rat)) * (4 + 6 * (1 / (n : Rat)) +
        4 * (1 / (n : Rat)) ^ 2 + (1 / (n : Rat)) ^ 3)) /
        ((1 / (n : Rat)) * 1) - 4) <=
      11 / (n : Rat) := by
  have hstage := quartic_linear_worked_remainder_at_stage hn
  rw [hstage]
  let x : Rat := 1 / (n : Rat)
  have hxpos : 0 < x := by
    dsimp [x]
    rw [Rat.div_def]
    exact Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hn))
  have hxle : x <= 1 := by
    dsimp [x]
    rw [Rat.div_def]
    apply Rat.le_of_mul_le_mul_right (c := (n : Rat))
    · have hne : (n : Rat) ≠ 0 := Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
      have hinv : (n : Rat)⁻¹ * n = 1 := by
        rw [Rat.mul_comm]
        exact Rat.mul_inv_cancel _ hne
      simp only [Rat.one_mul]
      rw [hinv]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))
    · exact (Rat.natCast_pos).2 hn
  have hsq : x * x <= x := by
    have h := Rat.mul_le_mul_of_nonneg_left hxle (Rat.le_of_lt hxpos)
    simpa [Rat.mul_one] using h
  have hcube : x ^ 3 <= x := by
    have hmul := Rat.mul_le_mul_of_nonneg_right hsq (Rat.le_of_lt hxpos)
    calc
      x ^ 3 = (x * x) * x := by
        simp [Rat.pow_succ, Rat.pow_zero, Rat.mul_assoc]
      _ <= x * x := hmul
      _ <= x := hsq
  have hnonneg : 0 <= 6 * x + 4 * x ^ 2 + x ^ 3 := by
    exact Rat.add_nonneg
      (Rat.add_nonneg
        (Rat.mul_nonneg (by native_decide) (Rat.le_of_lt hxpos))
        (Rat.mul_nonneg (by native_decide)
          (Rat.pow_nonneg (Rat.le_of_lt hxpos))))
      (Rat.pow_nonneg (Rat.le_of_lt hxpos))
  change qabs (6 * x + 4 * x ^ 2 + x ^ 3) <= 11 / (n : Rat)
  rw [qabs_eq_self_of_nonneg hnonneg]
  have hbound : 6 * x + 4 * x ^ 2 + x ^ 3 <= 11 * x := by
    grind [show x ^ 2 = x * x by
      simp [Rat.pow_succ, Rat.pow_zero, Rat.mul_assoc]]
  have hEleven : (11 : Rat) * x = 11 / (n : Rat) := by
    simp [x, Rat.div_def, Rat.mul_assoc]
  rw [← hEleven]
  exact hbound

/-! The quintic analogue: the residual after cancelling `(x-1)` from
`x^5-1` differs from its base value `5` by a finite quartic polynomial. -/

theorem quintic_linear_worked_remainder (step : Rat) (hstep : step ≠ 0) :
    (step * (5 + 10 * step + 10 * step ^ 2 + 5 * step ^ 3 + step ^ 4)) /
        (step * 1) - 5 =
      10 * step + 10 * step ^ 2 + 5 * step ^ 3 + step ^ 4 := by
  have hcancel : step * step⁻¹ = 1 := Rat.mul_inv_cancel _ hstep
  rw [Rat.div_def]
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem quintic_linear_worked_remainder_at_stage {n : Nat} (hn : 0 < n) :
    ((1 / (n : Rat)) * (5 + 10 * (1 / (n : Rat)) +
        10 * (1 / (n : Rat)) ^ 2 + 5 * (1 / (n : Rat)) ^ 3 +
        (1 / (n : Rat)) ^ 4)) /
        ((1 / (n : Rat)) * 1) - 5 =
      10 / (n : Rat) + 10 * (1 / (n : Rat)) ^ 2 +
        5 * (1 / (n : Rat)) ^ 3 + (1 / (n : Rat)) ^ 4 := by
  have hstep : (1 / (n : Rat)) ≠ 0 := by
    rw [Rat.div_def]
    exact Rat.ne_of_gt (Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hn)))
  have h := quintic_linear_worked_remainder (1 / (n : Rat)) hstep
  simpa [Rat.div_def, Rat.mul_assoc, Rat.mul_comm] using h

/-! The sextic analogue: the residual after cancelling `(x-1)` from
`x^6-1` differs from its base value `6` by a finite quintic polynomial. -/

theorem sextic_linear_worked_remainder (step : Rat) (hstep : step ≠ 0) :
    (step * (6 + 15 * step + 20 * step ^ 2 + 15 * step ^ 3 +
        6 * step ^ 4 + step ^ 5)) / (step * 1) - 6 =
      15 * step + 20 * step ^ 2 + 15 * step ^ 3 +
        6 * step ^ 4 + step ^ 5 := by
  have hcancel : step * step⁻¹ = 1 := Rat.mul_inv_cancel _ hstep
  rw [Rat.div_def]
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem sextic_linear_worked_remainder_at_stage {n : Nat} (hn : 0 < n) :
    ((1 / (n : Rat)) * (6 + 15 * (1 / (n : Rat)) +
        20 * (1 / (n : Rat)) ^ 2 + 15 * (1 / (n : Rat)) ^ 3 +
        6 * (1 / (n : Rat)) ^ 4 + (1 / (n : Rat)) ^ 5)) /
        ((1 / (n : Rat)) * 1) - 6 =
      15 / (n : Rat) + 20 * (1 / (n : Rat)) ^ 2 +
        15 * (1 / (n : Rat)) ^ 3 + 6 * (1 / (n : Rat)) ^ 4 +
        (1 / (n : Rat)) ^ 5 := by
  have hstep : (1 / (n : Rat)) ≠ 0 := by
    rw [Rat.div_def]
    exact Rat.ne_of_gt (Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hn)))
  have h := sextic_linear_worked_remainder (1 / (n : Rat)) hstep
  simpa [Rat.div_def, Rat.mul_assoc, Rat.mul_comm] using h

/-! The septic analogue: after cancelling `(x-1)` from `x^7-1`, the
residual quotient differs from its base value `7` by a finite sextic
polynomial. -/

theorem septic_linear_worked_remainder (step : Rat) (hstep : step ≠ 0) :
    (step * (7 + 21 * step + 35 * step ^ 2 + 35 * step ^ 3 +
        21 * step ^ 4 + 7 * step ^ 5 + step ^ 6)) / (step * 1) - 7 =
      21 * step + 35 * step ^ 2 + 35 * step ^ 3 +
        21 * step ^ 4 + 7 * step ^ 5 + step ^ 6 := by
  have hcancel : step * step⁻¹ = 1 := Rat.mul_inv_cancel _ hstep
  rw [Rat.div_def]
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem septic_linear_worked_remainder_at_stage {n : Nat} (hn : 0 < n) :
    ((1 / (n : Rat)) * (7 + 21 * (1 / (n : Rat)) +
        35 * (1 / (n : Rat)) ^ 2 + 35 * (1 / (n : Rat)) ^ 3 +
        21 * (1 / (n : Rat)) ^ 4 + 7 * (1 / (n : Rat)) ^ 5 +
        (1 / (n : Rat)) ^ 6)) /
        ((1 / (n : Rat)) * 1) - 7 =
      21 / (n : Rat) + 35 * (1 / (n : Rat)) ^ 2 +
        35 * (1 / (n : Rat)) ^ 3 + 21 * (1 / (n : Rat)) ^ 4 +
        7 * (1 / (n : Rat)) ^ 5 + (1 / (n : Rat)) ^ 6 := by
  have hstep : (1 / (n : Rat)) ≠ 0 := by
    rw [Rat.div_def]
    exact Rat.ne_of_gt (Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hn)))
  have h := septic_linear_worked_remainder (1 / (n : Rat)) hstep
  simpa [Rat.div_def, Rat.mul_assoc, Rat.mul_comm] using h

/-! The octic analogue continues the finite cancellation ladder without
introducing an attained limit. -/

theorem octic_linear_worked_remainder (step : Rat) (hstep : step ≠ 0) :
    (step * (8 + 28 * step + 56 * step ^ 2 + 70 * step ^ 3 +
        56 * step ^ 4 + 28 * step ^ 5 + 8 * step ^ 6 + step ^ 7)) /
        (step * 1) - 8 =
      28 * step + 56 * step ^ 2 + 70 * step ^ 3 +
        56 * step ^ 4 + 28 * step ^ 5 + 8 * step ^ 6 + step ^ 7 := by
  have hcancel : step * step⁻¹ = 1 := Rat.mul_inv_cancel _ hstep
  rw [Rat.div_def]
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem octic_linear_worked_remainder_at_stage {n : Nat} (hn : 0 < n) :
    ((1 / (n : Rat)) * (8 + 28 * (1 / (n : Rat)) +
        56 * (1 / (n : Rat)) ^ 2 + 70 * (1 / (n : Rat)) ^ 3 +
        56 * (1 / (n : Rat)) ^ 4 + 28 * (1 / (n : Rat)) ^ 5 +
        8 * (1 / (n : Rat)) ^ 6 + (1 / (n : Rat)) ^ 7)) /
        ((1 / (n : Rat)) * 1) - 8 =
      28 / (n : Rat) + 56 * (1 / (n : Rat)) ^ 2 +
        70 * (1 / (n : Rat)) ^ 3 + 56 * (1 / (n : Rat)) ^ 4 +
        28 * (1 / (n : Rat)) ^ 5 + 8 * (1 / (n : Rat)) ^ 6 +
        (1 / (n : Rat)) ^ 7 := by
  have hstep : (1 / (n : Rat)) ≠ 0 := by
    rw [Rat.div_def]
    exact Rat.ne_of_gt (Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hn)))
  have h := octic_linear_worked_remainder (1 / (n : Rat)) hstep
  simpa [Rat.div_def, Rat.mul_assoc, Rat.mul_comm] using h

/-! The degree-nine analogue matches the project's worked nonic MVT
checkpoint and keeps the quotient error entirely finite and rational. -/

theorem nonic_linear_worked_remainder (step : Rat) (hstep : step ≠ 0) :
    (step * (9 + 36 * step + 84 * step ^ 2 + 126 * step ^ 3 +
        126 * step ^ 4 + 84 * step ^ 5 + 36 * step ^ 6 +
        9 * step ^ 7 + step ^ 8)) / (step * 1) - 9 =
      36 * step + 84 * step ^ 2 + 126 * step ^ 3 + 126 * step ^ 4 +
        84 * step ^ 5 + 36 * step ^ 6 + 9 * step ^ 7 + step ^ 8 := by
  have hcancel : step * step⁻¹ = 1 := Rat.mul_inv_cancel _ hstep
  rw [Rat.div_def]
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem nonic_linear_worked_remainder_at_stage {n : Nat} (hn : 0 < n) :
    ((1 / (n : Rat)) * (9 + 36 * (1 / (n : Rat)) +
        84 * (1 / (n : Rat)) ^ 2 + 126 * (1 / (n : Rat)) ^ 3 +
        126 * (1 / (n : Rat)) ^ 4 + 84 * (1 / (n : Rat)) ^ 5 +
        36 * (1 / (n : Rat)) ^ 6 + 9 * (1 / (n : Rat)) ^ 7 +
        (1 / (n : Rat)) ^ 8)) / ((1 / (n : Rat)) * 1) - 9 =
      36 / (n : Rat) + 84 * (1 / (n : Rat)) ^ 2 +
        126 * (1 / (n : Rat)) ^ 3 + 126 * (1 / (n : Rat)) ^ 4 +
        84 * (1 / (n : Rat)) ^ 5 + 36 * (1 / (n : Rat)) ^ 6 +
        9 * (1 / (n : Rat)) ^ 7 + (1 / (n : Rat)) ^ 8 := by
  have hstep : (1 / (n : Rat)) ≠ 0 := by
    rw [Rat.div_def]
    exact Rat.ne_of_gt (Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hn)))
  have h := nonic_linear_worked_remainder (1 / (n : Rat)) hstep
  simpa [Rat.div_def, Rat.mul_assoc, Rat.mul_comm] using h

end FiniteLHopitalCertificate

end ComputableAnalysis
