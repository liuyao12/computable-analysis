import ComputableAnalysis.ModularForms.CMImaginaryCoordinates163

/-! Rational coordinate-box bounds for embedded integral CM lattice points. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163
open RiemannHilbert FunctionTheory

theorem complexRaw_small (u : QuadraticOrder163) (r : Rat) (hr : 0≤r)
    (hx : -r≤(u.x:Rat) ∧ (u.x:Rat)≤r)
    (hy : -r≤(u.y:Rat) ∧ (u.y:Rat)≤r) : Small u.complexRaw (82*r) := by
  have hre (n : Nat) := complexRaw_real_compute u n
  have him (n : Nat) := complexRaw_imag_compute u n
  have hib (n : Nat) : -(82*r)≤(u.complexRaw.compute n).hi.im ∧
      (u.complexRaw.compute n).lo.im≤82*r := by
    have hs := sqrt163_uniform_bounds n
    have ho := RealRaw.interval_order_of_valid sqrt163 sqrt163_valid n
    have hlo := congrArg QInterval.lo (him n)
    have hhi := congrArg QInterval.hi (him n)
    simp only [ComplexRaw.imagPart,RealRaw.scaleRat,RealRaw.scaleRatCompute] at hlo hhi
    by_cases hc : (0:Rat)≤(u.y:Rat)/2
    · simp only [if_pos hc] at hlo hhi
      rw [hlo,hhi]
      have hp := Rat.mul_le_mul_of_nonneg_left hs.2 hc
      have hn := Rat.mul_nonneg hc hs.1
      have hp' := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans ho hs.2) hc
      have hn' := Rat.mul_nonneg hc (Rat.le_trans hs.1 ho)
      grind
    · simp only [if_neg hc] at hlo hhi
      rw [hlo,hhi]
      have hp := Rat.mul_le_mul_of_nonneg_left hs.2 (show 0≤ -(u.y:Rat)/2 by grind)
      have hn := Rat.mul_nonneg (show 0≤ -(u.y:Rat)/2 by grind) hs.1
      have hp' := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans ho hs.2)
        (show 0≤ -(u.y:Rat)/2 by grind)
      have hn' := Rat.mul_nonneg (show 0≤ -(u.y:Rat)/2 by grind) (Rat.le_trans hs.1 ho)
      grind
  refine ⟨?_,?_,?_,?_⟩
  · intro n m
    have h := congrArg QInterval.hi (hre m)
    change (u.complexRaw.compute m).hi.re=(u.x:Rat)+(u.y:Rat)/2 at h
    change -(82*r)≤(u.complexRaw.compute m).hi.re
    rw [h]
    grind
  · intro n m
    have h := congrArg QInterval.lo (hre n)
    change (u.complexRaw.compute n).lo.re=(u.x:Rat)+(u.y:Rat)/2 at h
    change (u.complexRaw.compute n).lo.re≤82*r
    rw [h]
    grind
  · intro n m
    exact (hib m).1
  · intro n m
    exact (hib n).2

end ComputableAnalysis.ModularForms.QuadraticOrder163
