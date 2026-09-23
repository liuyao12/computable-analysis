import ComputableAnalysis.ComputableWeightedLogarithm

/-! Derivatives of constant multiples of the explicit logarithm charts. -/
namespace ComputableAnalysis
namespace ComputableLogarithmChart
open PrimitiveLogarithmEstimates

private theorem domain_bound {m : Coefficient} {c x : Rat}
    (hx : inDomainInterval (c-m.radius) (c+m.radius) x) : qabs (x-c) ≤ m.radius := by
  change c-m.radius ≤ x ∧ x ≤ c+m.radius at hx
  unfold qabs
  split <;> grind

def Coefficient.weightedValueOn (m : Coefficient) (imag : Bool) (c : Rat) : FunctionOnInterval :=
  FunctionOnInterval.ofStable
    { definedAt := fun x => qabs (x-c) ≤ m.radius
      compute := fun x => (rawCoordinate imag (m.weightedValue (x-c))).compute
      rate := fun _ => .unknown }
    (c-m.radius) (c+m.radius) (fun _ hx => domain_bound hx)
    (fun _ hx => rawCoordinate_valid imag (m.weightedValue_valid hx))

def Coefficient.weightedDerivativeOn (m : Coefficient) (imag : Bool) (c : Rat) : FunctionOnInterval :=
  FunctionOnInterval.ofStable
    { definedAt := fun x => qabs (x-c) ≤ m.radius
      compute := fun x => (rawCoordinate imag (m.weightedDerivative (x-c))).compute
      rate := fun _ => .unknown }
    (c-m.radius) (c+m.radius) (fun _ hx => domain_bound hx)
    (fun _ hx => rawCoordinate_valid imag (m.weightedDerivative_valid hx))

theorem Coefficient.weightedValue_coordinate_mem (m : Coefficient) (imag : Bool) {t : Rat}
    (ht : qabs t ≤ m.radius) (n : Nat) :
    ((rawCoordinate imag (m.weightedValue t)).compute n).lo ≤ coordinate imag (m.weightedValueSample t n) ∧
      coordinate imag (m.weightedValueSample t n) ≤ ((rawCoordinate imag (m.weightedValue t)).compute n).hi := by
  have H := m.weightedValue_contains_sample ht n
  cases imag
  · exact ⟨H.1.1, H.2.1⟩
  · exact ⟨H.1.2, H.2.2⟩

theorem Coefficient.weightedDerivative_coordinate_mem (m : Coefficient) (imag : Bool) {t : Rat}
    (ht : qabs t ≤ m.radius) (n : Nat) :
    ((rawCoordinate imag (m.weightedDerivative t)).compute n).lo ≤ coordinate imag (m.weightedDerivativeSample t n) ∧
      coordinate imag (m.weightedDerivativeSample t n) ≤ ((rawCoordinate imag (m.weightedDerivative t)).compute n).hi := by
  have H := m.weightedDerivative_contains_sample ht n
  cases imag
  · exact ⟨H.1.1, H.2.1⟩
  · exact ⟨H.1.2, H.2.2⟩

theorem Coefficient.weightedValue_width (m : Coefficient) (imag : Bool) (t : Rat) (n : Nat) :
    ((rawCoordinate imag (m.weightedValue t)).compute n).width ≤ 2*m.weightedValueRadius n := by
  have hr := ComplexRaw.cauchyStabilize_width_le_current_expand (candidate := pointStream (m.weightedValueSample t)) (radius := m.weightedValueRadius) n
  have hi := ComplexRaw.cauchyStabilize_height_le_current_expand (candidate := pointStream (m.weightedValueSample t)) (radius := m.weightedValueRadius) n
  cases imag
  · change ((m.weightedValue t).compute n).width ≤ _
    simpa only [weightedValue, weightedDerivative, pointStream, QBox.point, QBox.width, Rat.sub_self, Rat.zero_add] using hr
  · change ((m.weightedValue t).compute n).height ≤ _
    simpa only [weightedValue, weightedDerivative, pointStream, QBox.point, QBox.height, Rat.sub_self, Rat.zero_add] using hi

theorem Coefficient.weightedDerivative_width (m : Coefficient) (imag : Bool) (t : Rat) (n : Nat) :
    ((rawCoordinate imag (m.weightedDerivative t)).compute n).width ≤ 2*m.weightedDerivativeRadius n := by
  have hr := ComplexRaw.cauchyStabilize_width_le_current_expand (candidate := pointStream (m.weightedDerivativeSample t)) (radius := m.weightedDerivativeRadius) n
  have hi := ComplexRaw.cauchyStabilize_height_le_current_expand (candidate := pointStream (m.weightedDerivativeSample t)) (radius := m.weightedDerivativeRadius) n
  cases imag
  · change ((m.weightedDerivative t).compute n).width ≤ _
    simpa only [weightedValue, weightedDerivative, pointStream, QBox.point, QBox.width, Rat.sub_self, Rat.zero_add] using hr
  · change ((m.weightedDerivative t).compute n).height ≤ _
    simpa only [weightedValue, weightedDerivative, pointStream, QBox.point, QBox.height, Rat.sub_self, Rat.zero_add] using hi

def Coefficient.weightedRuntimeBound (m : Coefficient) (h : Rat) : Rat :=
  8*m.bound*m.bound + 4*m.valueBound*qabs h⁻¹ + 2*m.derivativeBound

theorem Coefficient.weightedRuntimeBound_nonneg (m : Coefficient) (h : Rat) : 0 ≤ m.weightedRuntimeBound h := by
  have hM := Rat.mul_nonneg (Rat.le_of_lt m.bound_pos) (Rat.le_of_lt m.bound_pos)
  have hv := Rat.mul_nonneg (Rat.le_of_lt m.valueBound_pos) (qabs_nonneg h⁻¹)
  have hd := m.derivativeBound_pos
  unfold weightedRuntimeBound
  grind

def Coefficient.weightedEvalStage (m : Coefficient) (h : Rat) (n : Nat) : Nat :=
  RationalMajorant.halfDecayShift (m.weightedRuntimeBound h) (halfTolerance (precisionAtStage n))

theorem Coefficient.weightedRuntime_budget (m : Coefficient) (h : Rat) (n : Nat) :
    m.weightedRuntimeBound h * half^(m.weightedEvalStage h n) ≤ (precisionAtStage n).val/2 :=
  RationalMajorant.halfDecayShift_spec (m.weightedRuntimeBound_nonneg h) (halfTolerance (precisionAtStage n))

def Coefficient.weightedStepStage (m : Coefficient) (n : Nat) : Nat :=
  2 ^ RationalMajorant.halfDecayShift (2*m.bound*m.bound*m.bound) (halfTolerance (precisionAtStage n))

theorem Coefficient.weightedStep_budget (m : Coefficient) (n : Nat) {h : Rat}
    (hs : qabs h ≤ 1/((m.weightedStepStage n : Nat) : Rat)) :
    2*m.bound*m.bound*m.bound*qabs h ≤ (precisionAtStage n).val/2 := by
  have hM := Rat.le_of_lt m.bound_pos
  have hc : 0 ≤ 2*m.bound*m.bound*m.bound := by have hsq := Rat.mul_nonneg hM hM; have := Rat.mul_nonneg hsq hM; grind
  have ht := RationalMajorant.halfDecayShift_spec hc (halfTolerance (precisionAtStage n))
  have hm := Rat.mul_le_mul_of_nonneg_left hs hc
  have he : 1/((m.weightedStepStage n : Nat) : Rat) = half ^
      RationalMajorant.halfDecayShift (2*m.bound*m.bound*m.bound) (halfTolerance (precisionAtStage n)) := by
    exact (RationalMajorant.half_pow_eq_one_div_nat_two_pow _).symm
  rw [he] at hm
  exact Rat.le_trans hm ht

/-- No derivative assumption: the same finite logarithm calculation works
for every certified computable complex coefficient. -/
def Coefficient.weightedFiniteModel (m : Coefficient) (imag : Bool) (c : Rat) :
    FiniteModelDerivativeOnInterval (m.weightedValueOn imag c) (m.weightedDerivativeOn imag c) where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := m.weightedStepStage
  evalPrecision := fun _ h n => m.weightedEvalStage h n
  baseValue := fun x h n => coordinate imag (m.weightedValueSample (x-c) (m.weightedEvalStage h n))
  stepValue := fun x h n => coordinate imag (m.weightedValueSample (x+h-c) (m.weightedEvalStage h n))
  derivativeValue := fun x h n => coordinate imag (m.weightedDerivativeSample (x-c) (m.weightedEvalStage h n))
  base_mem := fun _ _ _ hx _ => m.weightedValue_coordinate_mem imag (domain_bound hx) _
  step_mem := fun _ _ _ _ hx => m.weightedValue_coordinate_mem imag (domain_bound hx) _
  derivative_mem := fun _ _ _ hx => m.weightedDerivative_coordinate_mem imag (domain_bound hx) _
  secant_error := by
    intro x h n hx hxh hh hs
    let s := m.weightedEvalStage h n
    have he := m.weighted_prefix_secant (domain_bound hx)
      (show qabs ((x-c)+h) ≤ m.radius by
        have H := domain_bound hxh
        simpa only [show x+h-c = (x-c)+h by grind] using H) hh s
    have hp := coordinate_secant_le imag (m.weightedValueSample (x-c) s) (m.weightedValueSample (x+h-c) s)
      (m.weightedDerivativeSample (x-c) s) h
    have hsec : qabs ((coordinate imag (m.weightedValueSample (x+h-c) s)-coordinate imag (m.weightedValueSample (x-c) s))/h -
        coordinate imag (m.weightedDerivativeSample (x-c) s)) ≤ 2*m.bound*m.bound*m.bound*qabs h + 8*m.bound*m.bound*half^s := by
      apply Rat.le_trans hp
      simpa only [weightedValueSample, weightedDerivativeSample, show x+h-c=(x-c)+h by grind] using he
    have hstep := m.weightedStep_budget n hs
    have ht := m.weightedRuntime_budget h n
    have hb : 8*m.bound*m.bound ≤ m.weightedRuntimeBound h := by
      have hv := Rat.mul_nonneg (Rat.le_of_lt m.valueBound_pos) (qabs_nonneg h⁻¹)
      have hd := m.derivativeBound_pos
      unfold weightedRuntimeBound
      grind
    have htail := Rat.mul_le_mul_of_nonneg_right hb (Rat.pow_nonneg half_nonneg (n := s))
    change qabs _ ≤ _
    change m.weightedRuntimeBound h * half^s ≤ _ at ht
    grind
  quotient_width := by
    intro x h n hx hxh hh hs
    rw [QInterval.differenceQuotient_width]
    let s := m.weightedEvalStage h n
    have hwx := m.weightedValue_width imag (x-c) s
    have hwy := m.weightedValue_width imag (x+h-c) s
    have hm := Rat.mul_le_mul_of_nonneg_left (rat_add_le_add hwy hwx) (qabs_nonneg h⁻¹)
    have hb : 4*m.valueBound*qabs h⁻¹ ≤ m.weightedRuntimeBound h := by
      have hM := Rat.mul_nonneg (Rat.le_of_lt m.bound_pos) (Rat.le_of_lt m.bound_pos)
      have hd := m.derivativeBound_pos
      unfold weightedRuntimeBound
      grind
    have ht := m.weightedRuntime_budget h n
    have htail := Rat.mul_le_mul_of_nonneg_right hb (Rat.pow_nonneg half_nonneg (n := s))
    change qabs (1/h) * (((rawCoordinate imag (m.weightedValue (x+h-c))).compute s).width +
      ((rawCoordinate imag (m.weightedValue (x-c))).compute s).width) ≤ _
    simp only [Rat.div_def, Rat.one_mul]
    unfold weightedValueRadius at hm
    change m.weightedRuntimeBound h * half^s ≤ _ at ht
    have he := (precisionAtStage n).property
    grind
  derivative_width := by
    intro x h n hx
    let s := m.weightedEvalStage h n
    have hw := m.weightedDerivative_width imag (x-c) s
    have hb : 2*m.derivativeBound ≤ m.weightedRuntimeBound h := by
      have hM := Rat.mul_nonneg (Rat.le_of_lt m.bound_pos) (Rat.le_of_lt m.bound_pos)
      have hv := Rat.mul_nonneg (Rat.le_of_lt m.valueBound_pos) (qabs_nonneg h⁻¹)
      unfold weightedRuntimeBound
      grind
    have ht := m.weightedRuntime_budget h n
    have htail := Rat.mul_le_mul_of_nonneg_right hb (Rat.pow_nonneg half_nonneg (n := s))
    change ((rawCoordinate imag (m.weightedDerivative (x-c))).compute s).width ≤ _
    unfold weightedDerivativeRadius at hw
    change m.weightedRuntimeBound h * half^s ≤ _ at ht
    have he := (precisionAtStage n).property
    grind

def Coefficient.weightedHasDerivative (m : Coefficient) (imag : Bool) (c : Rat) :
    HasDerivativeOnInterval (m.weightedValueOn imag c) (m.weightedDerivativeOn imag c) :=
  (m.weightedFiniteModel imag c).toHasDerivativeOnInterval

end ComputableLogarithmChart
end ComputableAnalysis
