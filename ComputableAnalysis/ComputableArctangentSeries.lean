import ComputableAnalysis.ComputableLogarithmPrimitives

/-! The imaginary logarithm evaluator computes the usual arctangent series. -/
namespace ComputableAnalysis
namespace ComputableLogarithmChart
open ComplexLogarithmApproximation

def atanPartial (x : Rat) : Nat → Rat
  | 0 => 0
  | n+1 => atanPartial x n + ((-x*x)^n*x)/((2*n+1 : Nat) : Rat)

theorem imaginary_pow_even (x : Rat) (n : Nat) :
    QComplex.pow ⟨0,x⟩ (2*n) = ⟨(-x*x)^n, 0⟩ := by
  induction n with
  | zero => simp [QComplex.pow, QComplex.one]
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega, QComplex.pow, QComplex.pow, ih, Rat.pow_succ]
    simp only [QComplex.mul, Rat.mul_zero, Rat.zero_mul, Rat.add_zero, Rat.zero_add]
    congr 1 <;> grind

theorem imaginary_pow_odd (x : Rat) (n : Nat) :
    QComplex.pow ⟨0,x⟩ (2*n+1) = ⟨0, (-x*x)^n*x⟩ := by
  rw [QComplex.pow, imaginary_pow_even]
  simp only [QComplex.mul, Rat.mul_zero, Rat.zero_mul, Rat.add_zero, Rat.zero_add]
  congr 1 <;> grind

theorem log_imaginary_prefix (x : Rat) (n : Nat) :
    (logPrefix ⟨0,x⟩ (2*n)).im = atanPartial x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : FormalPowerSeries.altSign (2*n) = 1 := by
      unfold FormalPowerSeries.altSign
      have hm : 2*n % 2 = 0 := by omega
      rw [hm]
      rfl
    change (tailPartial ⟨0,x⟩ 0 (2*(n+1))).im = _
    rw [show 2*(n+1)=2*n+1+1 by omega, tailPartial, tailPartial]
    simp only [QComplex.add, Nat.zero_add, term, imaginary_pow_odd,
      show 2*n+1+1=2*(n+1) by omega, imaginary_pow_even, QComplex.scaleRat,
      QComplex.divRat, Rat.div_def, Rat.zero_mul, Rat.mul_zero, Rat.add_zero, he, Rat.one_mul]
    change (logPrefix ⟨0,x⟩ (2*n)).im + _ = _
    rw [ih]
    rfl

/-- Every even-stage candidate is literally a finite arctangent Taylor sum
at a certified rational approximation to the original computable coefficient. -/
theorem arctan_valueSample (scale : ComputableCoefficient.Value) (t : Rat) (n : Nat) :
    ((arctanChart scale).valueSample t (2*n)).im =
      atanPartial (t * scale.sample ((arctanChart scale).samples (2*n))) n := by
  change (logPrefix (QComplex.scaleRat t ((arctanChart scale).sample (2*n))) (2*n)).im = _
  have he : QComplex.scaleRat t ((arctanChart scale).sample (2*n)) =
      ⟨0, t * scale.sample ((arctanChart scale).samples (2*n))⟩ := by
    simp only [Coefficient.sample, arctanChart, ComputableCoefficient.Value.rational,
      QComplex.scaleRat, Rat.mul_zero]
  rw [he, log_imaginary_prefix]

end ComputableLogarithmChart
end ComputableAnalysis
