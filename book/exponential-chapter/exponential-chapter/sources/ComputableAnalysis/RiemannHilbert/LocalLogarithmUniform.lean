import ComputableAnalysis.RiemannHilbert.LocalLogarithmDerivative

/-! Constructed uniform value, derivative, remainder and Lipschitz bounds
for the actual Taylor logarithm chart. They support actual ODE comparisons
and exponential pullbacks, without pointwise-to-uniform assumptions. -/
namespace ComputableAnalysis.RiemannHilbert.LocalLogarithm
open ComplexRaw FunctionTheory LocalODE

theorem value_bound (z : Scalar) (hz : interior radius.val z) :
    Small (function.eval z hz).val 4 := by
  change Small (coefficientSum coefficient z.val coefficient_valid z.property 1 1 radius.val) 4
  simpa only [Rat.mul_one] using coefficientSum_bound coefficient z.val coefficient_valid z.property
    1 1 radius.val (by decide) (by decide) (by decide +kernel) coefficient_bound
    (interior_bound radius.val z hz) (by decide +kernel)

theorem derivative_bound (z : Scalar) (hz : interior radius.val z) :
    Small (derivativeValue z hz).val 4 := by
  change Small (ScalarSeries.value (BoundedSeries.derivativeTerm coefficient z.val)
    (BoundedSeries.derivativeTerm_valid coefficient z.val coefficient_valid z.property) (1*1) (4*1*radius.val)) 4
  have hb : ∀ k, Small (BoundedSeries.derivativeTerm coefficient z.val k) (2*(1*1)*(4*1*radius.val)^k) := by
    intro k
    simpa only [Rat.mul_assoc] using
      BoundedSeries.derivativeTerm_majorant coefficient z.val coefficient_valid z.property
        1 1 radius.val (by decide) (by decide) (by decide +kernel) coefficient_bound
        (interior_bound radius.val z hz) k
  have h := ScalarSeries.value_bound (BoundedSeries.derivativeTerm coefficient z.val)
    (BoundedSeries.derivativeTerm_valid coefficient z.val coefficient_valid z.property)
    (1*1) (4*1*radius.val) (by decide +kernel) (by decide +kernel) (by decide +kernel) hb
  simpa only [Rat.mul_one] using h

theorem quadratic_remainder (w z : Scalar) (hw : interior radius.val w) (hz : interior radius.val z)
    (H : Rat) (hH : 0 ≤ H) (hzw : Small (sub z.val w.val) H) :
    Small (DomainFunctions.remainder function w hw (derivativeValue w hw) z hz) (16*H^2) := by
  change Small (SeriesLimitLaws.remainder
    (BoundedSeries.sumValue coefficient z.val coefficient_valid z.property 1 1 radius.val)
    (BoundedSeries.sumValue coefficient w.val coefficient_valid w.property 1 1 radius.val)
    (BoundedSeries.sumDerivative coefficient w.val coefficient_valid w.property 1 1 radius.val)
    (sub z.val w.val)) (16*H^2)
  simpa only [Rat.mul_one, Rat.pow_succ, Rat.pow_zero] using
    BoundedSeries.sum_remainder_bound coefficient w.val z.val coefficient_valid w.property z.property
      1 1 radius.val H (by decide) (by decide) (by decide +kernel) hH coefficient_bound
      (interior_bound radius.val w hw) (interior_bound radius.val z hz) hzw (by decide +kernel)

def uniformDelta (eps : QPos) : QPos := derivativeDelta 1 1 (by decide) (by decide) eps

theorem uniform_remainder (eps H : QPos) (w z : Scalar) (hw : interior radius.val w) (hz : interior radius.val z)
    (hH : H.val ≤ (uniformDelta eps).val) (hzw : Small (sub z.val w.val) H.val) :
    Small (DomainFunctions.remainder function w hw (derivativeValue w hw) z hz) (eps.val*H.val) :=
  BoundedSeries.sum_derivative_error coefficient w.val z.val coefficient_valid w.property z.property
    1 1 radius.val (by decide) (by decide) (by decide +kernel) coefficient_bound
    (interior_bound radius.val w hw) (interior_bound radius.val z hz) (by decide +kernel) eps H hH hzw

theorem lipschitz (w z : Scalar) (hw : interior radius.val w) (hz : interior radius.val z)
    (H : QPos) (hzw : Small (sub z.val w.val) H.val) :
    Small (sub (function.eval z hz).val (function.eval w hw).val) (9*H.val) := by
  let h := if H.val ≤ 2*radius.val then H.val else 2*radius.val
  have hnonneg : 0 ≤ h := by dsimp [h]; have := H.property; have := radius.property; grind
  have hstep : Small (sub z.val w.val) h := by
    have hb := SeriesLimitLaws.small_sub (interior_bound radius.val z hz) (interior_bound radius.val w hw)
    have he : radius.val+radius.val=2*radius.val := by grind
    rw [he] at hb
    dsimp [h]
    by_cases hh : H.val ≤ 2*radius.val
    · simpa only [if_pos hh] using hzw
    · simpa only [if_neg hh] using hb
  have hr := quadratic_remainder w z hw hz h hnonneg hstep
  have hl := Small.mul (derivativeValue w hw).property (sub_valid z.property w.property)
    (by decide : (0 : Rat) ≤ 4) hnonneg (derivative_bound w hw) hstep
  have ha := small_add hl hr
  have he := SeriesLimitLaws.add_difference
    (sub (function.eval z hz).val (function.eval w hw).val)
    (mul (derivativeValue w hw).val (sub z.val w.val))
    (sub_valid (function.eval z hz).property (function.eval w hw).property)
    (mul_valid (derivativeValue w hw).property (sub_valid z.property w.property))
  apply (Small.congr (add_valid (mul_valid (derivativeValue w hw).property (sub_valid z.property w.property))
      (DomainFunctions.remainder_valid _ _ _ _ _ _))
    (sub_valid (function.eval z hz).property (function.eval w hw).property) he ha).mono
  have hh : h ≤ 2*radius.val ∧ h ≤ H.val := by dsimp [h]; grind
  have hm := Rat.mul_le_mul_of_nonneg_right hh.1 hnonneg
  have hn := Rat.mul_le_mul_of_nonneg_left hm (by decide : (0 : Rat) ≤ 16)
  have hrad : 16*(2*radius.val)=1 := by decide +kernel
  have heq : 16*(2*radius.val*h)=h := by
    rw [← Rat.mul_assoc, hrad, Rat.one_mul]
  rw [heq] at hn
  have hf := Rat.mul_le_mul_of_nonneg_left hh.2 (by decide : (0 : Rat) ≤ 9)
  simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
  calc
    2*4*h+16*(h*h) ≤ 2*4*h+h := rat_add_le_add (Rat.le_refl) hn
    _ = 9*h := by grind only
    _ ≤ 9*H.val := hf

end ComputableAnalysis.RiemannHilbert.LocalLogarithm
