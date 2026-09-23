import ComputableAnalysis.ComputableWeightedLogarithmDerivative
import ComputableAnalysis.ComputableLogarithmPrimitives

/-! Logarithm and normalized arctangent primitives of positive quadratics.
The quadratic is `(x-a)^2+b^2`, with computable `a,b` and certified `b ≠ 0`. -/
namespace ComputableAnalysis
namespace ComputableLogarithmChart
open PrimitiveLogarithmEstimates ComputableCoefficient

theorem Coefficient.weightedDerivative_equiv (m : Coefficient) (imag : Bool) (t : Rat)
    (ht : qabs t ≤ m.radius) (v : Value) (cutoff : Nat)
    (heq : ∀ n, cutoff ≤ n → ∀ s, Samples n s →
      m.weightCoefficient.sample s * coordinate imag
        (kernel ⟨m.realCoefficient.sample s, m.imagCoefficient.sample s⟩ t) = v.sample s) :
    (rawCoordinate imag (m.weightedDerivative t)).Equiv v.real.preferred := by
  intro k
  let n := max k (max cutoff (v.observation k))
  have hn : k ≤ n := Nat.le_max_left _ _
  have hs := m.index_le_stage n
  have hv := v.encloses k (m.stage n) (by dsimp [n] at *; omega) (m.samples n) (m.samples_valid n)
  have he := heq (m.stage n) (by dsimp [n] at *; omega) (m.samples n) (m.samples_valid n)
  have hd := m.weightedDerivative_coordinate_mem imag ht n
  have hh := (rawCoordinate_valid imag (m.weightedDerivative_valid ht)).2.1 k n hn
  have he' : coordinate imag (m.weightedDerivativeSample t n) = v.sample (m.samples n) := by
    cases imag <;> exact he
  rw [he'] at hd
  apply (RealRaw.compareAt_overlap_iff _ _ k k).2
  change ((rawCoordinate imag (m.weightedDerivative t)).compute k).lo ≤ (v.real.compute k).hi ∧
    (v.real.compute k).lo ≤ ((rawCoordinate imag (m.weightedDerivative t)).compute k).hi
  constructor <;> grind

private theorem kernel_inverse_shift (z : QComplex) (t : Rat)
    (hz : z.normSq ≠ 0) (hw : (QComplex.add z (QComplex.ofRat t)).normSq ≠ 0) :
    kernel z.inverse t = (QComplex.add z (QComplex.ofRat t)).inverse := by
  let w := QComplex.add z (QComplex.ofRat t)
  let A := QComplex.add QComplex.one (QComplex.scaleRat t z.inverse)
  have hzi := QComplex.mul_inverse_of_normSq_ne_zero z hz
  have hwi := QComplex.mul_inverse_of_normSq_ne_zero w hw
  have hA : A = QComplex.mul z.inverse w := by
    have hunit : QComplex.mul z.inverse z = QComplex.one := by rw [QComplex.mul_comm_cert]; exact hzi
    change QComplex.add QComplex.one (QComplex.scaleRat t z.inverse) = _
    rw [← hunit]
    simp only [A, w, QComplex.mul, QComplex.add, QComplex.scaleRat, QComplex.ofRat]
    congr 1 <;> grind
  have hAinv : QComplex.mul A (QComplex.mul w.inverse z) = QComplex.one := by
    rw [hA, QComplex.mul_assoc_cert, ← QComplex.mul_assoc_cert w w.inverse z, hwi,
      QComplex.one_mul_cert, QComplex.mul_comm_cert]
    exact hzi
  have hAn : A.normSq ≠ 0 := by
    intro he
    have hz0 := QComplex.normSq_eq_zero_iff.mp he
    rw [hz0] at hAinv
    have hh : (0 : Rat) = 1 := by
      have := congrArg QComplex.re hAinv
      simpa only [QComplex.mul, QComplex.zero, QComplex.one, Rat.zero_mul, Rat.sub_eq_add_neg,
        Rat.neg_zero, Rat.add_zero] using this
    exact (by decide +kernel : (0 : Rat) ≠ 1) hh
  have hAi := QComplex.mul_inverse_of_normSq_ne_zero A hAn
  have hAf : A.inverse = QComplex.mul w.inverse z := by
    calc
      A.inverse = QComplex.mul A.inverse QComplex.one := (QComplex.mul_one_cert _).symm
      _ = QComplex.mul A.inverse (QComplex.mul A (QComplex.mul w.inverse z)) := by rw [hAinv]
      _ = QComplex.mul (QComplex.mul A.inverse A) (QComplex.mul w.inverse z) := (QComplex.mul_assoc_cert _ _ _).symm
      _ = QComplex.mul w.inverse z := by rw [QComplex.mul_comm_cert A.inverse A, hAi, QComplex.one_mul_cert]
  change QComplex.mul z.inverse A.inverse = w.inverse
  rw [hAf, QComplex.mul_comm_cert w.inverse z, ← QComplex.mul_assoc_cert,
    QComplex.mul_comm_cert z.inverse z, hzi, QComplex.one_mul_cert]

private theorem normSq_ne_zero_of_im_ne {a b : Rat} (hb : b ≠ 0) :
    (⟨a,b⟩ : QComplex).normSq ≠ 0 := by
  intro h
  have he := QComplex.normSq_eq_zero_iff.mp h
  exact hb (congrArg QComplex.im he)

def quadraticValue (pole width : Value) (x : Rat) : Value :=
  let d := Value.sub (.rational x) pole
  Value.add (Value.mul d d) (Value.mul width width)

/-- `normInverse` is the checked reciprocal of `(center-a)^2+b^2`. -/
def quadraticChart (pole width normInverse weight : Value) (center : Rat) : Coefficient :=
  ⟨Value.mul (Value.sub (.rational center) pole) normInverse,
    Value.neg (Value.mul width normInverse), weight⟩

private theorem quadratic_sample_kernel (pole width normInverse : Value) (center x : Rat) (N : Nat)
    (hi : (quadraticValue pole width center).inv? N = some normInverse)
    (s : Real → Rat) (hb : width.sample s ≠ 0) :
    kernel ⟨(quadraticChart pole width normInverse (.rational 1) center).realCoefficient.sample s,
      (quadraticChart pole width normInverse (.rational 1) center).imagCoefficient.sample s⟩ (x-center) =
      (⟨x-pole.sample s, width.sample s⟩ : QComplex).inverse := by
  have he := Value.inv?_sample _ _ N hi s
  simp only [quadraticValue, Value.sub, Value.add, Value.neg, Value.mul, Value.rational,
    ← Rat.sub_eq_add_neg] at he
  have hm : (⟨(quadraticChart pole width normInverse (.rational 1) center).realCoefficient.sample s,
      (quadraticChart pole width normInverse (.rational 1) center).imagCoefficient.sample s⟩ : QComplex) =
      (⟨center-pole.sample s, width.sample s⟩ : QComplex).inverse := by
    simp only [quadraticChart, Value.sub, Value.add, Value.neg, Value.mul, Value.rational,
      QComplex.inverse, QComplex.normSq, Rat.div_def, ← Rat.sub_eq_add_neg, he]
    congr 1 <;> grind
  rw [hm]
  have hw : QComplex.add ⟨center-pole.sample s, width.sample s⟩ (QComplex.ofRat (x-center)) =
      ⟨x-pole.sample s, width.sample s⟩ := by
    simp only [QComplex.add, QComplex.ofRat]
    congr 1 <;> grind
  have H := kernel_inverse_shift ⟨center-pole.sample s, width.sample s⟩ (x-center)
    (normSq_ne_zero_of_im_ne hb) (by rw [hw]; exact normSq_ne_zero_of_im_ne hb)
  rw [hw] at H
  exact H

/-- The real logarithm coordinate gives the logarithm of the quadratic ratio. -/
def quadraticLog_hasDerivative (pole width normInverse : Value) (center : Rat) :
    HasDerivativeOnInterval
      ((quadraticChart pole width normInverse (.rational 2) center).weightedValueOn false center)
      ((quadraticChart pole width normInverse (.rational 2) center).weightedDerivativeOn false center) :=
  (quadraticChart pole width normInverse (.rational 2) center).weightedHasDerivative false center

/-- The imaginary coordinate, multiplied by `-1/b`, is the normalized
arctangent difference with derivative `1/((x-a)^2+b^2)`. -/
def quadraticArctan_hasDerivative (pole width normInverse widthInverse : Value) (center : Rat) :
    HasDerivativeOnInterval
      ((quadraticChart pole width normInverse (Value.neg widthInverse) center).weightedValueOn true center)
      ((quadraticChart pole width normInverse (Value.neg widthInverse) center).weightedDerivativeOn true center) :=
  (quadraticChart pole width normInverse (Value.neg widthInverse) center).weightedHasDerivative true center

theorem quadraticArctan_derivative_equiv (pole width normInverse widthInverse target : Value)
    (center x : Rat) (N M K : Nat)
    (hn : (quadraticValue pole width center).inv? N = some normInverse)
    (hb : width.inv? M = some widthInverse)
    (ht : (quadraticValue pole width x).inv? K = some target)
    (hx : qabs (x-center) ≤ (quadraticChart pole width normInverse (Value.neg widthInverse) center).radius) :
    (rawCoordinate true ((quadraticChart pole width normInverse (Value.neg widthInverse) center).weightedDerivative (x-center))).Equiv
      target.real.preferred := by
  apply Coefficient.weightedDerivative_equiv _ true _ hx target (width.observation M)
  intro n hcut s hs
  have hbn := Value.inverse_sample_apart width widthInverse M hb n hcut s hs
  have hi := Value.inv?_sample _ _ M hb s
  have hv := Value.inv?_sample _ _ K ht s
  have hk := quadratic_sample_kernel pole width normInverse center x N hn s hbn
  change -widthInverse.sample s * coordinate true
    (kernel ⟨(Value.mul (Value.sub (.rational center) pole) normInverse).sample s,
      (Value.neg (Value.mul width normInverse)).sample s⟩ (x-center)) = target.sample s
  simp only [quadraticChart] at hk
  rw [hi, hk]
  simp only [quadraticValue, Value.sub, Value.add, Value.neg, Value.mul, Value.rational,
    ← Rat.sub_eq_add_neg] at hv
  rw [hv]
  simp only [coordinate, if_true, QComplex.inverse, QComplex.normSq, Rat.div_def]
  have hc := Rat.inv_mul_cancel (width.sample s) hbn
  grind

/-- The real logarithm coordinate differentiates to the quadratic's
logarithmic derivative, using the original computable coefficients. -/
theorem quadraticLog_derivative_equiv (pole width normInverse widthInverse target : Value)
    (center x : Rat) (N M K : Nat)
    (hn : (quadraticValue pole width center).inv? N = some normInverse)
    (hb : width.inv? M = some widthInverse)
    (ht : (quadraticValue pole width x).inv? K = some target)
    (hx : qabs (x-center) ≤ (quadraticChart pole width normInverse (.rational 2) center).radius) :
    (rawCoordinate false ((quadraticChart pole width normInverse (.rational 2) center).weightedDerivative (x-center))).Equiv
      (Value.mul (.rational 2) (Value.mul (Value.sub (.rational x) pole) target)).real.preferred := by
  apply Coefficient.weightedDerivative_equiv _ false _ hx _ (width.observation M)
  intro n hcut s hs
  have hbn := Value.inverse_sample_apart width widthInverse M hb n hcut s hs
  have hv := Value.inv?_sample _ _ K ht s
  have hk := quadratic_sample_kernel pole width normInverse center x N hn s hbn
  simp only [quadraticChart] at hk
  change 2 * coordinate false (kernel
    ⟨(Value.mul (Value.sub (.rational center) pole) normInverse).sample s,
      (Value.neg (Value.mul width normInverse)).sample s⟩ (x-center)) = _
  rw [hk]
  simp only [coordinate, Bool.false_eq_true, if_false, QComplex.inverse, QComplex.normSq,
    quadraticValue, Value.sub, Value.add, Value.neg, Value.mul, Value.rational,
    ← Rat.sub_eq_add_neg] at hv ⊢
  rw [hv]
  rfl

end ComputableLogarithmChart
end ComputableAnalysis
