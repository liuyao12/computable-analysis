import ComputableAnalysis.ComputableCoefficientApproximation
import ComputableAnalysis.PrimitiveLogarithmEstimates
import ComputableAnalysis.FiniteDerivativeLimit

/-!
# Concrete logarithm charts with computable coefficients

The evaluator computes finite prefixes of `log(1 + m (x-c))`. Both coordinates
of `m` are arbitrary certified real computations. Rational coefficient
approximations are synchronized at the two endpoints of every secant.
-/
namespace ComputableAnalysis
namespace ComputableLogarithmChart
open PrimitiveLogarithmEstimates ComplexLogarithmApproximation

structure Coefficient where
  realCoefficient : ComputableCoefficient.Value
  imagCoefficient : ComputableCoefficient.Value
  weightCoefficient : ComputableCoefficient.Value := .rational 1

def Coefficient.re (m : Coefficient) : Real := m.realCoefficient.real
def Coefficient.im (m : Coefficient) : Real := m.imagCoefficient.real
def Coefficient.weight (m : Coefficient) : Real := m.weightCoefficient.real

def Coefficient.ofReals (re im : Real) : Coefficient :=
  ⟨.parameter re, .parameter im, .rational 1⟩

def tolerance (n : Nat) : QPos := ⟨half^n, Rat.pow_pos (by decide +kernel)⟩

def Coefficient.request (m : Coefficient) (n : Nat) : Nat :=
  max n (max (m.realCoefficient.observation 0) (max (m.imagCoefficient.observation 0)
    (max (m.weightCoefficient.observation 0)
      (max (m.realCoefficient.observation (ComputableCoefficient.widthStage m.re (tolerance n)))
        (max (m.imagCoefficient.observation (ComputableCoefficient.widthStage m.im (tolerance n)))
          (m.weightCoefficient.observation (ComputableCoefficient.widthStage m.weight (tolerance n))))))))

def Coefficient.stage (m : Coefficient) : Nat → Nat
  | 0 => m.request 0
  | n+1 => max (m.stage n) (m.request (n+1))

theorem Coefficient.request_le_stage (m : Coefficient) (n : Nat) : m.request n ≤ m.stage n := by
  cases n with
  | zero => exact Nat.le_refl _
  | succ n => exact Nat.le_max_right _ _

theorem Coefficient.index_le_stage (m : Coefficient) (n : Nat) : n ≤ m.stage n :=
  Nat.le_trans (Nat.le_max_left _ _) (m.request_le_stage n)

theorem Coefficient.stage_mono (m : Coefficient) {k n : Nat} (h : k ≤ n) : m.stage k ≤ m.stage n := by
  induction n with
  | zero =>
    have hk : k=0 := by omega
    subst k
    exact Nat.le_refl _
  | succ n ih =>
    by_cases he : k=n+1
    · subst k; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (Nat.le_max_left _ _)

def Coefficient.samples (m : Coefficient) (n : Nat) : Real → Rat :=
  fun x => (x.compute (m.stage n)).lo

def Coefficient.sample (m : Coefficient) (n : Nat) : QComplex :=
  ⟨m.realCoefficient.sample (m.samples n), m.imagCoefficient.sample (m.samples n)⟩

theorem Coefficient.samples_valid (m : Coefficient) (n : Nat) :
    ComputableCoefficient.Samples (m.stage n) (m.samples n) :=
  ComputableCoefficient.samples_lower _

theorem Coefficient.sample_mem (m : Coefficient) {k n : Nat} (hkn : k ≤ n) :
    let R := m.re.compute (ComputableCoefficient.widthStage m.re (tolerance k))
    let I := m.im.compute (ComputableCoefficient.widthStage m.im (tolerance k))
    R.lo ≤ (m.sample n).re ∧ (m.sample n).re ≤ R.hi ∧
    I.lo ≤ (m.sample n).im ∧ (m.sample n).im ≤ I.hi := by
  have hs := m.request_le_stage k
  have hn := m.stage_mono hkn
  unfold request at hs
  have hr := m.realCoefficient.encloses (ComputableCoefficient.widthStage m.re (tolerance k))
    (m.stage n) (by omega) (m.samples n) (m.samples_valid n)
  have hi := m.imagCoefficient.encloses (ComputableCoefficient.widthStage m.im (tolerance k))
    (m.stage n) (by omega) (m.samples n) (m.samples_valid n)
  exact ⟨hr.1, hr.2, hi.1, hi.2⟩

theorem Coefficient.sample_future (m : Coefficient) {k n : Nat} (h : k ≤ n) :
    QComplex.normBound (QComplex.sub (m.sample n) (m.sample k)) ≤ 2*half^k := by
  have hn := m.sample_mem h
  have hk := m.sample_mem (Nat.le_refl k)
  have hr := qabs_sub_le_of_common_bounds hn.1 hn.2.1 hk.1 hk.2.1
  have hi := qabs_sub_le_of_common_bounds hn.2.2.1 hn.2.2.2 hk.2.2.1 hk.2.2.2
  have hwr := ComputableCoefficient.widthStage_spec m.re (tolerance k)
  have hwi := ComputableCoefficient.widthStage_spec m.im (tolerance k)
  change _ ≤ half^k at hwr hwi
  unfold QInterval.width at hwr hwi
  simp only [QComplex.normBound, QComplex.sub, QComplex.add, QComplex.neg, ← Rat.sub_eq_add_neg]
  grind

def Coefficient.bound (m : Coefficient) : Rat :=
  qabs (m.re.compute 0).lo + qabs (m.re.compute 0).hi +
  qabs (m.im.compute 0).lo + qabs (m.im.compute 0).hi +
  qabs (m.weight.compute 0).lo + qabs (m.weight.compute 0).hi + 1

theorem Coefficient.bound_pos (m : Coefficient) : 0 < m.bound := by
  have := qabs_nonneg (m.re.compute 0).lo
  have := qabs_nonneg (m.re.compute 0).hi
  have := qabs_nonneg (m.im.compute 0).lo
  have := qabs_nonneg (m.im.compute 0).hi
  have := qabs_nonneg (m.weight.compute 0).lo
  have := qabs_nonneg (m.weight.compute 0).hi
  unfold bound
  grind

private theorem sample_abs_bound {a b v : Rat} (hv : a ≤ v ∧ v ≤ b) :
    qabs v ≤ qabs a + qabs b := by
  have hl := neg_qabs_le_self a
  have hu := self_le_qabs b
  have hn1 := qabs_nonneg a
  have hn2 := qabs_nonneg b
  unfold qabs
  split <;> grind

theorem Coefficient.sample_bound (m : Coefficient) (n : Nat) :
    QComplex.normBound (m.sample n) ≤ m.bound := by
  have hs := m.request_le_stage n
  unfold request at hs
  have hr := m.realCoefficient.encloses 0 (m.stage n) (by omega) (m.samples n) (m.samples_valid n)
  have hi := m.imagCoefficient.encloses 0 (m.stage n) (by omega) (m.samples n) (m.samples_valid n)
  have hrb := sample_abs_bound hr
  have hib := sample_abs_bound hi
  change qabs (m.realCoefficient.sample (m.samples n)) + qabs (m.imagCoefficient.sample (m.samples n)) ≤ _
  have := qabs_nonneg (m.weight.compute 0).lo
  have := qabs_nonneg (m.weight.compute 0).hi
  unfold bound re im
  grind

def Coefficient.weightSample (m : Coefficient) (n : Nat) : Rat :=
  m.weightCoefficient.sample (m.samples n)

theorem Coefficient.weightSample_mem (m : Coefficient) {k n : Nat} (hkn : k ≤ n) :
    let I := m.weight.compute (ComputableCoefficient.widthStage m.weight (tolerance k))
    I.lo ≤ m.weightSample n ∧ m.weightSample n ≤ I.hi := by
  have hs := m.request_le_stage k
  have hn := m.stage_mono hkn
  unfold request at hs
  exact m.weightCoefficient.encloses _ (m.stage n) (by omega) (m.samples n) (m.samples_valid n)

theorem Coefficient.weightSample_future (m : Coefficient) {k n : Nat} (hkn : k ≤ n) :
    qabs (m.weightSample n-m.weightSample k) ≤ half^k := by
  have hn := m.weightSample_mem hkn
  have hk := m.weightSample_mem (Nat.le_refl k)
  have hd := qabs_sub_le_of_common_bounds hn.1 hn.2 hk.1 hk.2
  exact Rat.le_trans hd (ComputableCoefficient.widthStage_spec m.weight (tolerance k))

theorem Coefficient.weightSample_bound (m : Coefficient) (n : Nat) : qabs (m.weightSample n) ≤ m.bound := by
  have hs := m.request_le_stage n
  unfold request at hs
  have h := m.weightCoefficient.encloses 0 (m.stage n) (by omega) (m.samples n) (m.samples_valid n)
  have hw := sample_abs_bound h
  have := qabs_nonneg (m.re.compute 0).lo
  have := qabs_nonneg (m.re.compute 0).hi
  have := qabs_nonneg (m.im.compute 0).lo
  have := qabs_nonneg (m.im.compute 0).hi
  unfold weightSample bound weight
  grind

def Coefficient.radius (m : Coefficient) : Rat := 1/(2*m.bound)

theorem Coefficient.radius_pos (m : Coefficient) : 0 < m.radius := by
  unfold radius
  rw [Rat.div_def, Rat.one_mul]
  exact Rat.inv_pos.mpr (Rat.mul_pos (by decide +kernel) m.bound_pos)

theorem Coefficient.bound_mul_radius (m : Coefficient) : m.bound*m.radius = half := by
  have hc := Rat.mul_inv_cancel m.bound (Rat.ne_of_gt m.bound_pos)
  unfold radius half
  rw [Rat.div_def, Rat.inv_mul_rev]
  grind

theorem Coefficient.argument_bound (m : Coefficient) {t : Rat} (ht : qabs t ≤ m.radius) (n : Nat) :
    QComplex.normBound (QComplex.scaleRat t (m.sample n)) ≤ half := by
  rw [QComplex.normBound_scaleRat]
  have h1 := Rat.mul_le_mul_of_nonneg_left (m.sample_bound n) (qabs_nonneg t)
  have h2 := Rat.mul_le_mul_of_nonneg_right ht (Rat.le_of_lt m.bound_pos)
  have h3 := m.bound_mul_radius
  grind

def pointStream (f : Nat → QComplex) : ComplexRaw where
  compute := fun n => QBox.point (f n)

theorem geometric_shrinks {C : Rat} (hC : 0 ≤ C) : ShrinksToZero (fun n => C*half^n) := by
  intro eps
  refine ⟨RationalMajorant.halfDecayShift C eps, ?_⟩
  intro n hn
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left (half_pow_antitone hn) hC)
    (RationalMajorant.halfDecayShift_spec hC eps)

theorem pointStream_shrinks (f : Nat → QComplex) :
    ComplexRaw.WidthsShrinkToZero (pointStream f).compute := by
  intro eps
  refine ⟨0, ?_⟩
  intro n _
  constructor <;> simpa [pointStream, QBox.point, QBox.width, QBox.height, Rat.sub_self]
    using Rat.le_of_lt eps.property

def Coefficient.valueSample (m : Coefficient) (t : Rat) (n : Nat) : QComplex :=
  logPrefix (QComplex.scaleRat t (m.sample n)) n

def Coefficient.valueRadius (m : Coefficient) (n : Nat) : Rat := (4*m.radius+1)*half^n

def Coefficient.derivativeSample (m : Coefficient) (t : Rat) (n : Nat) : QComplex :=
  kernel (m.sample n) t

def Coefficient.derivativeRadius (m : Coefficient) (n : Nat) : Rat :=
  (2*(8+64*m.bound*m.radius))*half^n

theorem Coefficient.value_future (m : Coefficient) {t : Rat} (ht : qabs t ≤ m.radius)
    {k n : Nat} (hkn : k ≤ n) :
    QComplex.normBound (QComplex.sub (m.valueSample t n) (m.valueSample t k)) ≤ m.valueRadius k := by
  let u := QComplex.scaleRat t (m.sample n)
  let v := QComplex.scaleRat t (m.sample k)
  have hu := m.argument_bound ht n
  have hv := m.argument_bound ht k
  have htail := tailPartial_normBound_le_stageRadius hu k (n-k)
  have hadd := logPrefix_add u k (n-k)
  rw [show k+(n-k)=n by omega] at hadd
  have hd : QComplex.sub (logPrefix u n) (logPrefix v k) =
      QComplex.add (tailPartial u k (n-k)) (QComplex.sub (logPrefix u k) (logPrefix v k)) := by
    rw [hadd]
    simp only [QComplex.sub, QComplex.add, QComplex.neg]
    congr 1 <;> grind
  have huv : QComplex.sub u v = QComplex.scaleRat t (QComplex.sub (m.sample n) (m.sample k)) := by
    simp only [u, v, QComplex.sub, QComplex.add, QComplex.neg, QComplex.scaleRat]
    congr 1 <;> grind
  have hdiff := m.sample_future hkn
  have hnorm : QComplex.normBound (QComplex.sub u v) ≤ 2*m.radius*half^k := by
    rw [huv, QComplex.normBound_scaleRat]
    have h1 := Rat.mul_le_mul_of_nonneg_left hdiff (qabs_nonneg t)
    have h2 := Rat.mul_le_mul_of_nonneg_right ht
      (Rat.mul_nonneg (by decide +kernel : (0 : Rat) ≤ 2) (Rat.pow_nonneg half_nonneg (n := k)))
    grind
  have hl := prefix_lipschitz hu hv k
  change QComplex.normBound (QComplex.sub (logPrefix u n) (logPrefix v k)) ≤ _
  rw [hd]
  have hs := QComplex.normBound_add_le (tailPartial u k (n-k)) (QComplex.sub (logPrefix u k) (logPrefix v k))
  rw [stageRadius_eq_half_pow] at htail
  change QComplex.normBound _ ≤ half^k at htail
  unfold valueRadius
  grind

theorem Coefficient.derivative_future (m : Coefficient) {t : Rat} (ht : qabs t ≤ m.radius)
    {k n : Nat} (hkn : k ≤ n) :
    QComplex.normBound (QComplex.sub (m.derivativeSample t n) (m.derivativeSample t k)) ≤ m.derivativeRadius k := by
  have hl := kernel_lipschitz (m.sample_bound n) (m.sample_bound k) (Rat.le_of_lt m.bound_pos)
    (Rat.le_of_lt m.radius_pos) ht (by rw [m.bound_mul_radius]; exact Rat.le_refl)
  have hf := m.sample_future hkn
  have hK : 0 ≤ 8+64*m.bound*m.radius := by
    have h := Rat.mul_nonneg (Rat.le_of_lt m.bound_pos) (Rat.le_of_lt m.radius_pos)
    grind
  have hm := Rat.mul_le_mul_of_nonneg_left hf hK
  change QComplex.normBound _ ≤ _
  unfold derivativeSample derivativeRadius
  grind

theorem point_future {f : Nat → QComplex} {r : Nat → Rat}
    (hf : ∀ k n, k ≤ n → QComplex.normBound (QComplex.sub (f n) (f k)) ≤ r k) :
    ∀ k n, k ≤ n → ((pointStream f).compute n).NestedIn
      (QBox.expand ((pointStream f).compute k) (r k)) := by
  intro k n h
  have he : f n = QComplex.add (f k) (QComplex.sub (f n) (f k)) := by
    cases hn : f n
    cases hk : f k
    simp only [QComplex.add, QComplex.sub, QComplex.neg]
    congr 1 <;> grind
  change (QBox.point (f n)).NestedIn (QBox.expand (QBox.point (f k)) (r k))
  rw [he]
  exact ComplexExponentialApproximation.point_add_error_nested_expand _ _ (hf k n h)

def Coefficient.value (m : Coefficient) (t : Rat) : ComplexRaw :=
  ComplexRaw.cauchyStabilize (pointStream (m.valueSample t)) m.valueRadius

def Coefficient.derivative (m : Coefficient) (t : Rat) : ComplexRaw :=
  ComplexRaw.cauchyStabilize (pointStream (m.derivativeSample t)) m.derivativeRadius

theorem Coefficient.value_valid (m : Coefficient) {t : Rat} (ht : qabs t ≤ m.radius) : (m.value t).Valid := by
  apply ComplexRaw.cauchyStabilize_valid
  · intro n; exact QComplex.le_refl _
  · exact pointStream_shrinks _
  · exact point_future (fun _ _ h => m.value_future ht h)
  · exact geometric_shrinks (by have := m.radius_pos; grind)

theorem Coefficient.derivative_valid (m : Coefficient) {t : Rat} (ht : qabs t ≤ m.radius) : (m.derivative t).Valid := by
  apply ComplexRaw.cauchyStabilize_valid
  · intro n; exact QComplex.le_refl _
  · exact pointStream_shrinks _
  · exact point_future (fun _ _ h => m.derivative_future ht h)
  · exact geometric_shrinks (by have := m.bound_mul_radius; have := half_nonneg; grind)

theorem Coefficient.value_contains_sample (m : Coefficient) {t : Rat} (ht : qabs t ≤ m.radius) (n : Nat) :
    (QBox.point (m.valueSample t n)).NestedIn ((m.value t).compute n) :=
  ComplexRaw.cauchyStabilize_contains_current (point_future (fun _ _ h => m.value_future ht h)) n

theorem Coefficient.derivative_contains_sample (m : Coefficient) {t : Rat} (ht : qabs t ≤ m.radius) (n : Nat) :
    (QBox.point (m.derivativeSample t n)).NestedIn ((m.derivative t).compute n) :=
  ComplexRaw.cauchyStabilize_contains_current (point_future (fun _ _ h => m.derivative_future ht h)) n

end ComputableLogarithmChart
end ComputableAnalysis
