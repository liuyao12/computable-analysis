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

end FiniteLHopitalCertificate

end ComputableAnalysis
