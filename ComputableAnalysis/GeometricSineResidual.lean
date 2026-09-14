import ComputableAnalysis.GeometricSineSecant

namespace ComputableAnalysis
namespace GeometricSineSecant

open ArctanGeometry GeometricRotationODE

/-- The first-quadrant cosine coordinate has the elementary rational bound. -/
theorem cosine_coordinate_bounds {u : Rat} (hu0 : 0 <= u) (hu1 : u <= 1) :
    0 <= pointRe u ∧ pointRe u <= 1 := by
  have hs0 := Rat.mul_nonneg hu0 hu0
  have hs1 := Rat.mul_le_mul_of_nonneg_left hu1 hu0
  simp only [Rat.mul_one] at hs1
  have hk := kernel_bounds hu0 hu1
  have hk0 : 0 <= integralKernel u := by grind
  have hn0 : 0 <= 1-u*u := by grind
  have hn1 : 1-u*u <= 1 := by grind
  have heq : pointRe u = (1-u*u)*integralKernel u := by
    unfold pointRe RationalCircle.Stage.point integralKernel
    simp only [Rat.div_def, Rat.one_mul]
  rw [heq]
  constructor
  · exact Rat.mul_nonneg hn0 hk0
  · have h1 := Rat.mul_le_mul_of_nonneg_right hn1 hk0
    simp only [Rat.one_mul] at h1
    exact Rat.le_trans h1 hk.2

/-- Velocity divided by angular speed is the cosine coordinate. -/
theorem sine_velocity_identity (u : Rat) :
    pointImDerivative u = 2*pointRe u*integralKernel u := by
  unfold pointImDerivative pointRe RationalCircle.Stage.pointDerivative
    RationalCircle.Stage.point integralKernel
  simp only [Rat.div_def, Rat.inv_mul_rev, Rat.one_mul]
  grind

private theorem sine_coordinate_residual
    {u v : Rat} (hu0 : 0 <= u) (hu1 : u <= 1)
    (hv0 : 0 <= v) (hv1 : v <= 1) :
    qabs (pointIm v-pointIm u-(v-u)*pointImDerivative u) <=
      12*qabs (v-u)*qabs (v-u) := by
  by_cases heq : v-u = 0
  · have huv : v = u := by grind
    subst v
    have hz : qabs (0 : Rat) = 0 := by decide +kernel
    simp only [Rat.sub_self, Rat.zero_mul, Rat.mul_zero, hz]
    exact Rat.le_refl
  · have hcancel : u+(v-u) = v := by grind
    have h := pointIm_secant_error_le_twelve hu0 hu1
      (by simpa only [hcancel] using hv0)
      (by simpa only [hcancel] using hv1) heq
    rw [hcancel] at h
    have hmul := Rat.mul_le_mul_of_nonneg_left h (qabs_nonneg (v-u))
    have hc := Rat.mul_inv_cancel (v-u) heq
    have hid : pointIm v-pointIm u-(v-u)*pointImDerivative u =
        (v-u)*((pointIm v-pointIm u)/(v-u)-pointImDerivative u) := by
      simp only [Rat.div_def]
      grind
    rw [hid, qabs_mul]
    simpa only [Rat.mul_assoc, Rat.mul_comm] using hmul

/-- A fully finite sine/angle residual estimate.  The two clock outputs may
be chosen independently anywhere inside their rational enclosures. -/
theorem sine_angle_residual
    {u v a b : Rat}
    (hu0 : 0 <= u) (hu1 : u <= 1) (hv0 : 0 <= v) (hv1 : v <= 1)
    (n : Nat)
    (ha0 : (arctanIntegralRectangleCompute v n).lo <= a)
    (ha1 : a <= (arctanIntegralRectangleCompute v n).hi)
    (hb0 : (arctanIntegralRectangleCompute u n).lo <= b)
    (hb1 : b <= (arctanIntegralRectangleCompute u n).hi) :
    qabs (pointIm v-pointIm u-2*pointRe u*(a-b)) <=
      20*qabs (v-u)*qabs (v-u) +
        2*((arctanIntegralRectangleCompute u n).width +
          (arctanIntegralRectangleCompute v n).width) := by
  have hs := sine_coordinate_residual hu0 hu1 hv0 hv1
  have ha := (clock_bounds hu0 hu1 hv0 hv1 n ha0 ha1 hb0 hb1).1
  have hc := cosine_coordinate_bounds hu0 hu1
  have h2c0 : 0 <= 2*pointRe u := Rat.mul_nonneg (by decide) hc.1
  have h2c2 : 2*pointRe u <= 2 := by
    have h := Rat.mul_le_mul_of_nonneg_left hc.2 (by decide : (0 : Rat) <= 2)
    simpa only [Rat.mul_one] using h
  have hmul1 := Rat.mul_le_mul_of_nonneg_right h2c2
    (qabs_nonneg (a-b-(v-u)*integralKernel u))
  have hmul2 := Rat.mul_le_mul_of_nonneg_left ha (by decide : (0 : Rat) <= 2)
  have hid : pointIm v-pointIm u-2*pointRe u*(a-b) =
      (pointIm v-pointIm u-(v-u)*pointImDerivative u) -
        (2*pointRe u)*(a-b-(v-u)*integralKernel u) := by
    rw [sine_velocity_identity]
    grind
  have htri := qabs_sub_le
    (pointIm v-pointIm u-(v-u)*pointImDerivative u)
    ((2*pointRe u)*(a-b-(v-u)*integralKernel u))
  rw [qabs_mul, qabs_eq_self_of_nonneg h2c0] at htri
  rw [hid]
  grind

end GeometricSineSecant
end ComputableAnalysis
