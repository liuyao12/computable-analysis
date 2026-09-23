import ComputableAnalysis.ComputableLogarithmChart

/-! Concrete two-sided derivatives of computable logarithm/arctangent charts. -/
namespace ComputableAnalysis
namespace ComputableLogarithmChart
open PrimitiveLogarithmEstimates

def coordinate (imag : Bool) (z : QComplex) : Rat := if imag then z.im else z.re

def rawCoordinate (imag : Bool) (z : ComplexRaw) : RealRaw :=
  if imag then z.imagPart else z.realPart

theorem rawCoordinate_valid (imag : Bool) {z : ComplexRaw} (hz : z.Valid) :
    (rawCoordinate imag z).Valid := by
  cases imag
  · exact ComplexRaw.realPart_valid hz
  · exact ComplexRaw.imagPart_valid hz

theorem coordinate_abs_le (imag : Bool) (z : QComplex) : qabs (coordinate imag z) ≤ z.normBound := by
  have hr := qabs_nonneg z.re
  have hi := qabs_nonneg z.im
  cases imag <;> simp only [coordinate, Bool.false_eq_true, if_false, if_true, QComplex.normBound] <;> grind

theorem coordinate_secant_le (imag : Bool) (A B D : QComplex) (h : Rat) :
    qabs ((coordinate imag B - coordinate imag A)/h - coordinate imag D) ≤
      QComplex.normBound (QComplex.sub (QComplex.scaleRat h⁻¹ (QComplex.sub B A)) D) := by
  have H := coordinate_abs_le imag (QComplex.sub (QComplex.scaleRat h⁻¹ (QComplex.sub B A)) D)
  cases imag <;>
    simpa only [coordinate, Bool.false_eq_true, if_false, if_true, QComplex.sub, QComplex.add,
      QComplex.neg, QComplex.scaleRat, Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_comm] using H

private theorem domain_bound {m : Coefficient} {c x : Rat}
    (hx : inDomainInterval (c-m.radius) (c+m.radius) x) : qabs (x-c) ≤ m.radius := by
  change c-m.radius ≤ x ∧ x ≤ c+m.radius at hx
  unfold qabs
  split <;> grind

def Coefficient.valueOn (m : Coefficient) (imag : Bool) (c : Rat) : FunctionOnInterval :=
  FunctionOnInterval.ofStable
    { definedAt := fun x => qabs (x-c) ≤ m.radius
      compute := fun x => (rawCoordinate imag (m.value (x-c))).compute
      rate := fun _ => .unknown }
    (c-m.radius) (c+m.radius) (fun _ hx => domain_bound hx)
    (fun _ hx => rawCoordinate_valid imag (m.value_valid hx))

def Coefficient.derivativeOn (m : Coefficient) (imag : Bool) (c : Rat) : FunctionOnInterval :=
  FunctionOnInterval.ofStable
    { definedAt := fun x => qabs (x-c) ≤ m.radius
      compute := fun x => (rawCoordinate imag (m.derivative (x-c))).compute
      rate := fun _ => .unknown }
    (c-m.radius) (c+m.radius) (fun _ hx => domain_bound hx)
    (fun _ hx => rawCoordinate_valid imag (m.derivative_valid hx))

theorem Coefficient.value_coordinate_mem (m : Coefficient) (imag : Bool) {t : Rat}
    (ht : qabs t ≤ m.radius) (n : Nat) :
    ((rawCoordinate imag (m.value t)).compute n).lo ≤ coordinate imag (m.valueSample t n) ∧
      coordinate imag (m.valueSample t n) ≤ ((rawCoordinate imag (m.value t)).compute n).hi := by
  have H := m.value_contains_sample ht n
  cases imag
  · exact ⟨H.1.1, H.2.1⟩
  · exact ⟨H.1.2, H.2.2⟩

theorem Coefficient.derivative_coordinate_mem (m : Coefficient) (imag : Bool) {t : Rat}
    (ht : qabs t ≤ m.radius) (n : Nat) :
    ((rawCoordinate imag (m.derivative t)).compute n).lo ≤ coordinate imag (m.derivativeSample t n) ∧
      coordinate imag (m.derivativeSample t n) ≤ ((rawCoordinate imag (m.derivative t)).compute n).hi := by
  have H := m.derivative_contains_sample ht n
  cases imag
  · exact ⟨H.1.1, H.2.1⟩
  · exact ⟨H.1.2, H.2.2⟩

theorem Coefficient.value_width (m : Coefficient) (imag : Bool) (t : Rat) (n : Nat) :
    ((rawCoordinate imag (m.value t)).compute n).width ≤ 2*m.valueRadius n := by
  have hr := ComplexRaw.cauchyStabilize_width_le_current_expand (candidate := pointStream (m.valueSample t)) (radius := m.valueRadius) n
  have hi := ComplexRaw.cauchyStabilize_height_le_current_expand (candidate := pointStream (m.valueSample t)) (radius := m.valueRadius) n
  cases imag
  · change ((m.value t).compute n).width ≤ _
    simpa only [value, derivative, pointStream, QBox.point, QBox.width, Rat.sub_self, Rat.zero_add] using hr
  · change ((m.value t).compute n).height ≤ _
    simpa only [value, derivative, pointStream, QBox.point, QBox.height, Rat.sub_self, Rat.zero_add] using hi

theorem Coefficient.derivative_width (m : Coefficient) (imag : Bool) (t : Rat) (n : Nat) :
    ((rawCoordinate imag (m.derivative t)).compute n).width ≤ 2*m.derivativeRadius n := by
  have hr := ComplexRaw.cauchyStabilize_width_le_current_expand (candidate := pointStream (m.derivativeSample t)) (radius := m.derivativeRadius) n
  have hi := ComplexRaw.cauchyStabilize_height_le_current_expand (candidate := pointStream (m.derivativeSample t)) (radius := m.derivativeRadius) n
  cases imag
  · change ((m.derivative t).compute n).width ≤ _
    simpa only [value, derivative, pointStream, QBox.point, QBox.width, Rat.sub_self, Rat.zero_add] using hr
  · change ((m.derivative t).compute n).height ≤ _
    simpa only [value, derivative, pointStream, QBox.point, QBox.height, Rat.sub_self, Rat.zero_add] using hi

def halfTolerance (e : QPos) : QPos := ⟨e.val/2, by
  rw [Rat.div_def]; exact Rat.mul_pos e.property (Rat.inv_pos.mpr (by decide +kernel))⟩

def Coefficient.runtimeBound (m : Coefficient) (h : Rat) : Rat :=
  8*m.bound + 4*(4*m.radius+1)*qabs h⁻¹ + 4*(8+64*m.bound*m.radius)

theorem Coefficient.runtimeBound_nonneg (m : Coefficient) (h : Rat) : 0 ≤ m.runtimeBound h := by
  have hM := m.bound_pos
  have hr := m.radius_pos
  have hh := qabs_nonneg h⁻¹
  have hm := Rat.mul_nonneg (Rat.le_of_lt hM) (Rat.le_of_lt hr)
  have hp := Rat.mul_nonneg (show 0 ≤ 4*m.radius+1 by grind) hh
  unfold runtimeBound
  grind

def Coefficient.evalStage (m : Coefficient) (h : Rat) (n : Nat) : Nat :=
  RationalMajorant.halfDecayShift (m.runtimeBound h) (halfTolerance (precisionAtStage n))

theorem Coefficient.runtime_budget (m : Coefficient) (h : Rat) (n : Nat) :
    m.runtimeBound h * half^(m.evalStage h n) ≤ (precisionAtStage n).val/2 :=
  RationalMajorant.halfDecayShift_spec (m.runtimeBound_nonneg h) (halfTolerance (precisionAtStage n))

def Coefficient.stepStage (m : Coefficient) (n : Nat) : Nat :=
  2 ^ RationalMajorant.halfDecayShift (2*m.bound*m.bound) (halfTolerance (precisionAtStage n))

theorem Coefficient.step_budget (m : Coefficient) (n : Nat) {h : Rat}
    (hs : qabs h ≤ 1/((m.stepStage n : Nat) : Rat)) :
    2*m.bound*m.bound*qabs h ≤ (precisionAtStage n).val/2 := by
  have hM := Rat.le_of_lt m.bound_pos
  have hc : 0 ≤ 2*m.bound*m.bound := by have := Rat.mul_nonneg hM hM; grind
  have ht := RationalMajorant.halfDecayShift_spec hc (halfTolerance (precisionAtStage n))
  have hm := Rat.mul_le_mul_of_nonneg_left hs hc
  have he : 1/((m.stepStage n : Nat) : Rat) = half ^
      RationalMajorant.halfDecayShift (2*m.bound*m.bound) (halfTolerance (precisionAtStage n)) := by
    exact (RationalMajorant.half_pow_eq_one_div_nat_two_pow _).symm
  rw [he] at hm
  exact Rat.le_trans hm ht

/-- No derivative assumption: the same finite logarithm calculation works
for every certified computable complex coefficient. -/
def Coefficient.finiteModel (m : Coefficient) (imag : Bool) (c : Rat) :
    FiniteModelDerivativeOnInterval (m.valueOn imag c) (m.derivativeOn imag c) where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := m.stepStage
  evalPrecision := fun _ h n => m.evalStage h n
  baseValue := fun x h n => coordinate imag (m.valueSample (x-c) (m.evalStage h n))
  stepValue := fun x h n => coordinate imag (m.valueSample (x+h-c) (m.evalStage h n))
  derivativeValue := fun x h n => coordinate imag (m.derivativeSample (x-c) (m.evalStage h n))
  base_mem := fun _ _ _ hx _ => m.value_coordinate_mem imag (domain_bound hx) _
  step_mem := fun _ _ _ _ hx => m.value_coordinate_mem imag (domain_bound hx) _
  derivative_mem := fun _ _ _ hx => m.derivative_coordinate_mem imag (domain_bound hx) _
  secant_error := by
    intro x h n hx hxh hh hs
    let s := m.evalStage h n
    have he := prefix_affine_secant (Rat.le_of_lt m.bound_pos) (m.sample_bound s)
      (m.argument_bound (domain_bound hx) s)
      (m.argument_bound (t := (x-c)+h) (by
        have H := domain_bound hxh
        simpa only [show x+h-c = (x-c)+h by grind] using H) s) hh s
    have hp := coordinate_secant_le imag (m.valueSample (x-c) s) (m.valueSample (x+h-c) s)
      (m.derivativeSample (x-c) s) h
    have hsec : qabs ((coordinate imag (m.valueSample (x+h-c) s)-coordinate imag (m.valueSample (x-c) s))/h -
        coordinate imag (m.derivativeSample (x-c) s)) ≤ 2*m.bound*m.bound*qabs h + 8*m.bound*half^s := by
      apply Rat.le_trans hp
      simpa only [valueSample, derivativeSample, show x+h-c=(x-c)+h by grind] using he
    have hstep := m.step_budget n hs
    have ht := m.runtime_budget h n
    have hb : 8*m.bound ≤ m.runtimeBound h := by
      have hM := Rat.le_of_lt m.bound_pos
      have hr := Rat.le_of_lt m.radius_pos
      have hh := qabs_nonneg h⁻¹
      have hm := Rat.mul_nonneg hM hr
      have hp := Rat.mul_nonneg (show 0 ≤ 4*m.radius+1 by grind) hh
      unfold runtimeBound
      grind
    have htail := Rat.mul_le_mul_of_nonneg_right hb (Rat.pow_nonneg half_nonneg (n := s))
    change qabs _ ≤ _
    change m.runtimeBound h * half^s ≤ _ at ht
    grind
  quotient_width := by
    intro x h n hx hxh hh hs
    rw [QInterval.differenceQuotient_width]
    let s := m.evalStage h n
    have hwx := m.value_width imag (x-c) s
    have hwy := m.value_width imag (x+h-c) s
    have hm := Rat.mul_le_mul_of_nonneg_left (rat_add_le_add hwy hwx) (qabs_nonneg h⁻¹)
    have hb : 4*(4*m.radius+1)*qabs h⁻¹ ≤ m.runtimeBound h := by
      have hM := Rat.le_of_lt m.bound_pos
      have hr := Rat.le_of_lt m.radius_pos
      have hp := Rat.mul_nonneg hM hr
      unfold runtimeBound
      grind
    have ht := m.runtime_budget h n
    have htail := Rat.mul_le_mul_of_nonneg_right hb (Rat.pow_nonneg half_nonneg (n := s))
    change qabs (1/h) * (((rawCoordinate imag (m.value (x+h-c))).compute s).width +
      ((rawCoordinate imag (m.value (x-c))).compute s).width) ≤ _
    simp only [Rat.div_def, Rat.one_mul]
    unfold valueRadius at hm
    change m.runtimeBound h * half^s ≤ _ at ht
    have he := (precisionAtStage n).property
    grind
  derivative_width := by
    intro x h n hx
    let s := m.evalStage h n
    have hw := m.derivative_width imag (x-c) s
    have hb : 4*(8+64*m.bound*m.radius) ≤ m.runtimeBound h := by
      have hM := Rat.le_of_lt m.bound_pos
      have hr := Rat.le_of_lt m.radius_pos
      have hh := qabs_nonneg h⁻¹
      have hp := Rat.mul_nonneg (show 0 ≤ 4*m.radius+1 by grind) hh
      unfold runtimeBound
      grind
    have ht := m.runtime_budget h n
    have htail := Rat.mul_le_mul_of_nonneg_right hb (Rat.pow_nonneg half_nonneg (n := s))
    change ((rawCoordinate imag (m.derivative (x-c))).compute s).width ≤ _
    unfold derivativeRadius at hw
    change m.runtimeBound h * half^s ≤ _ at ht
    have he := (precisionAtStage n).property
    grind

def Coefficient.hasDerivative (m : Coefficient) (imag : Bool) (c : Rat) :
    HasDerivativeOnInterval (m.valueOn imag c) (m.derivativeOn imag c) :=
  (m.finiteModel imag c).toHasDerivativeOnInterval

end ComputableLogarithmChart
end ComputableAnalysis
