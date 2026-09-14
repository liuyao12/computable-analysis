import MathlibComparison.TrigonometryBridge

/-! The Mathlib-side integral calculation. This is deliberately separate
from the still-required identification of the native quadrature program
with Mathlib's interval integral. It is not labelled a third native proof. -/
namespace MathlibComparison

/-- Mathlib's basepoint formula, with the normalized rational-angle scale. -/
theorem mathlib_cosine_primitive (t : ℝ) :
    (∫ x in (0 : ℝ)..t, Real.cos (Real.pi*x)) = Real.sin (Real.pi*t)/Real.pi := by
  have h := intervalIntegral.mul_integral_comp_mul_left (f := Real.cos)
    (a := (0 : ℝ)) (b := t) Real.pi
  rw [mul_zero,integral_cos,Real.sin_zero,sub_zero] at h
  apply (eq_div_iff Real.pi_ne_zero).2
  simpa only [mul_comm] using h

end MathlibComparison
