import ComputableAnalysis.ComputableLogarithmDerivative

/-! Computable constant multiples of the concrete logarithm charts. -/
namespace ComputableAnalysis
namespace ComputableLogarithmChart
open PrimitiveLogarithmEstimates ComplexLogarithmApproximation ComplexLogarithmJet

theorem Coefficient.valueSample_bound (m : Coefficient) {t : Rat} (ht : qabs t ≤ m.radius) (n : Nat) :
    QComplex.normBound (m.valueSample t n) ≤ 1 := by
  have h := tailPartial_normBound_le_stageRadius (m.argument_bound ht n) 0 n
  rw [stageRadius_eq_half_pow, Rat.pow_zero] at h
  exact h

theorem Coefficient.derivativeSample_bound (m : Coefficient) {t : Rat} (ht : qabs t ≤ m.radius) (n : Nat) :
    QComplex.normBound (m.derivativeSample t n) ≤ 8*m.bound := by
  have hi := inverse_one_add_normBound_le_eight (m.argument_bound ht n)
  have hm := m.sample_bound n
  have h1 := QComplex.normBound_mul_le (m.sample n)
    (QComplex.inverse (QComplex.add QComplex.one (QComplex.scaleRat t (m.sample n))))
  have h2 := Rat.mul_le_mul_of_nonneg_left hi (QComplex.normBound_nonneg (m.sample n))
  change QComplex.normBound _ ≤ _
  unfold derivativeSample kernel
  grind

def Coefficient.weightedValueSample (m : Coefficient) (t : Rat) (n : Nat) : QComplex :=
  QComplex.scaleRat (m.weightSample n) (m.valueSample t n)

def Coefficient.weightedDerivativeSample (m : Coefficient) (t : Rat) (n : Nat) : QComplex :=
  QComplex.scaleRat (m.weightSample n) (m.derivativeSample t n)

def Coefficient.valueBound (m : Coefficient) : Rat := m.bound*(4*m.radius+1)+1

def Coefficient.derivativeBound (m : Coefficient) : Rat := m.bound*(2*(8+64*m.bound*m.radius))+8*m.bound

theorem Coefficient.valueBound_pos (m : Coefficient) : 0 < m.valueBound := by
  have hM := m.bound_pos
  have hr := m.radius_pos
  have hp := Rat.mul_pos hM (show 0 < 4*m.radius+1 by grind)
  unfold valueBound
  grind

theorem Coefficient.derivativeBound_pos (m : Coefficient) : 0 < m.derivativeBound := by
  have hM := m.bound_pos
  have hr := m.radius_pos
  have hprod := Rat.mul_pos hM hr
  have hp := Rat.mul_pos hM (show 0 < 2*(8+64*m.bound*m.radius) by grind)
  unfold derivativeBound
  grind

def Coefficient.weightedValueRadius (m : Coefficient) (n : Nat) : Rat := m.valueBound*half^n

def Coefficient.weightedDerivativeRadius (m : Coefficient) (n : Nat) : Rat := m.derivativeBound*half^n

private theorem scale_difference_bound {a b : Rat} {z w : QComplex} {A B C D : Rat}
    (ha : qabs a ≤ A) (hab : qabs (a-b) ≤ B)
    (hz : QComplex.normBound (QComplex.sub z w) ≤ C) (hw : QComplex.normBound w ≤ D)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    QComplex.normBound (QComplex.sub (QComplex.scaleRat a z) (QComplex.scaleRat b w)) ≤ A*C+B*D := by
  have he : QComplex.sub (QComplex.scaleRat a z) (QComplex.scaleRat b w) =
      QComplex.add (QComplex.scaleRat a (QComplex.sub z w)) (QComplex.scaleRat (a-b) w) := by
    simp only [QComplex.sub, QComplex.add, QComplex.neg, QComplex.scaleRat]
    congr 1 <;> grind
  rw [he]
  have h1 := QComplex.normBound_add_le (QComplex.scaleRat a (QComplex.sub z w)) (QComplex.scaleRat (a-b) w)
  rw [QComplex.normBound_scaleRat, QComplex.normBound_scaleRat] at h1
  have h2 := Rat.mul_le_mul_of_nonneg_right ha (QComplex.normBound_nonneg (QComplex.sub z w))
  have h3 := Rat.mul_le_mul_of_nonneg_left hz hA
  have h4 := Rat.mul_le_mul_of_nonneg_right hab (QComplex.normBound_nonneg w)
  have h5 := Rat.mul_le_mul_of_nonneg_left hw hB
  grind

theorem Coefficient.weightedValue_future (m : Coefficient) {t : Rat} (ht : qabs t ≤ m.radius)
    {k n : Nat} (hkn : k ≤ n) :
    QComplex.normBound (QComplex.sub (m.weightedValueSample t n) (m.weightedValueSample t k)) ≤ m.weightedValueRadius k := by
  have h := scale_difference_bound (m.weightSample_bound n) (m.weightSample_future hkn)
    (m.value_future ht hkn) (m.valueSample_bound ht k) (Rat.le_of_lt m.bound_pos) (Rat.pow_nonneg half_nonneg)
  change QComplex.normBound _ ≤ _
  unfold weightedValueSample weightedValueRadius valueBound
  unfold valueRadius at h
  grind

theorem Coefficient.weightedDerivative_future (m : Coefficient) {t : Rat} (ht : qabs t ≤ m.radius)
    {k n : Nat} (hkn : k ≤ n) :
    QComplex.normBound (QComplex.sub (m.weightedDerivativeSample t n) (m.weightedDerivativeSample t k)) ≤ m.weightedDerivativeRadius k := by
  have h := scale_difference_bound (m.weightSample_bound n) (m.weightSample_future hkn)
    (m.derivative_future ht hkn) (m.derivativeSample_bound ht k) (Rat.le_of_lt m.bound_pos) (Rat.pow_nonneg half_nonneg)
  change QComplex.normBound _ ≤ _
  unfold weightedDerivativeSample weightedDerivativeRadius derivativeBound
  unfold derivativeRadius at h
  grind

def Coefficient.weightedValue (m : Coefficient) (t : Rat) : ComplexRaw :=
  ComplexRaw.cauchyStabilize (pointStream (m.weightedValueSample t)) m.weightedValueRadius

def Coefficient.weightedDerivative (m : Coefficient) (t : Rat) : ComplexRaw :=
  ComplexRaw.cauchyStabilize (pointStream (m.weightedDerivativeSample t)) m.weightedDerivativeRadius

theorem Coefficient.weightedValue_valid (m : Coefficient) {t : Rat} (ht : qabs t ≤ m.radius) : (m.weightedValue t).Valid := by
  apply ComplexRaw.cauchyStabilize_valid
  · intro n; exact QComplex.le_refl _
  · exact pointStream_shrinks _
  · exact point_future (fun _ _ h => m.weightedValue_future ht h)
  · exact geometric_shrinks (Rat.le_of_lt m.valueBound_pos)

theorem Coefficient.weightedDerivative_valid (m : Coefficient) {t : Rat} (ht : qabs t ≤ m.radius) : (m.weightedDerivative t).Valid := by
  apply ComplexRaw.cauchyStabilize_valid
  · intro n; exact QComplex.le_refl _
  · exact pointStream_shrinks _
  · exact point_future (fun _ _ h => m.weightedDerivative_future ht h)
  · exact geometric_shrinks (Rat.le_of_lt m.derivativeBound_pos)

theorem Coefficient.weightedValue_contains_sample (m : Coefficient) {t : Rat} (ht : qabs t ≤ m.radius) (n : Nat) :
    (QBox.point (m.weightedValueSample t n)).NestedIn ((m.weightedValue t).compute n) :=
  ComplexRaw.cauchyStabilize_contains_current (point_future (fun _ _ h => m.weightedValue_future ht h)) n

theorem Coefficient.weightedDerivative_contains_sample (m : Coefficient) {t : Rat} (ht : qabs t ≤ m.radius) (n : Nat) :
    (QBox.point (m.weightedDerivativeSample t n)).NestedIn ((m.weightedDerivative t).compute n) :=
  ComplexRaw.cauchyStabilize_contains_current (point_future (fun _ _ h => m.weightedDerivative_future ht h)) n

theorem Coefficient.weighted_prefix_secant (m : Coefficient) {t h : Rat}
    (ht : qabs t ≤ m.radius) (hth : qabs (t+h) ≤ m.radius) (hh : h ≠ 0) (n : Nat) :
    QComplex.normBound (QComplex.sub (QComplex.scaleRat h⁻¹
      (QComplex.sub (m.weightedValueSample (t+h) n) (m.weightedValueSample t n)))
      (m.weightedDerivativeSample t n)) ≤
      2*m.bound*m.bound*m.bound*qabs h + 8*m.bound*m.bound*half^n := by
  have hs := prefix_affine_secant (Rat.le_of_lt m.bound_pos) (m.sample_bound n)
    (m.argument_bound ht n) (m.argument_bound hth n) hh n
  have he : QComplex.sub (QComplex.scaleRat h⁻¹
      (QComplex.sub (m.weightedValueSample (t+h) n) (m.weightedValueSample t n)))
      (m.weightedDerivativeSample t n) = QComplex.scaleRat (m.weightSample n)
        (QComplex.sub (QComplex.scaleRat h⁻¹ (QComplex.sub (m.valueSample (t+h) n) (m.valueSample t n)))
          (m.derivativeSample t n)) := by
    simp only [weightedValueSample, weightedDerivativeSample, QComplex.sub, QComplex.add, QComplex.neg, QComplex.scaleRat]
    congr 1 <;> grind
  rw [he, QComplex.normBound_scaleRat]
  have h1 := Rat.mul_le_mul_of_nonneg_right (m.weightSample_bound n) (QComplex.normBound_nonneg
    (QComplex.sub (QComplex.scaleRat h⁻¹ (QComplex.sub (m.valueSample (t+h) n) (m.valueSample t n))) (m.derivativeSample t n)))
  have h2 := Rat.mul_le_mul_of_nonneg_left hs (Rat.le_of_lt m.bound_pos)
  change m.bound * QComplex.normBound (QComplex.sub (QComplex.scaleRat h⁻¹
    (QComplex.sub (m.valueSample (t+h) n) (m.valueSample t n))) (m.derivativeSample t n)) ≤ _ at h2
  grind

end ComputableLogarithmChart
end ComputableAnalysis
