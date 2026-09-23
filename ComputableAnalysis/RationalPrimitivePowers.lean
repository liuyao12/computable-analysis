import ComputableAnalysis.DifferentialSynchronizedSum

/-!
# Analytic primitives of repeated linear poles

Finite monomial secants, applied to the reciprocal coordinate, give actual
primitive certificates on any rational interval with an explicit denominator
separation. The sign of the denominator is unrestricted.
-/

namespace ComputableAnalysis
namespace RationalPrimitivePowers

open FinitePolynomial

/-- A repeated linear pole primitive, with pole order two more than `n`. -/
def primitive (pole : Rat) (n : Nat) (x : Rat) : Rat :=
  -((x - pole)⁻¹ ^ (n + 1) / ((n + 1 : Nat) : Rat))

def errorCoefficient (C : Rat) (n : Nat) : Rat :=
  (C * C) * (C * C * powerSecantErrorBound C (n + 1) + C * C ^ n)

theorem errorCoefficient_nonneg {C : Rat} (hC : 0 <= C) (n : Nat) :
    0 <= errorCoefficient C n := by
  exact Rat.mul_nonneg (Rat.mul_nonneg hC hC)
    (Rat.add_nonneg
      (Rat.mul_nonneg (Rat.mul_nonneg hC hC) (powerSecantErrorBound_nonneg hC _))
      (Rat.mul_nonneg hC (Rat.pow_nonneg hC)))

/-- The rational secant estimate holds on either side of a pole. -/
theorem secant_error {pole x h C : Rat} (hh : h ≠ 0)
    (hx : x - pole ≠ 0) (hxh : x + h - pole ≠ 0) (hC : 1 <= C)
    (hu : qabs (x - pole)⁻¹ <= C) (hv : qabs (x + h - pole)⁻¹ <= C)
    (n : Nat) :
    qabs ((primitive pole n (x + h) - primitive pole n x) / h -
      (x - pole)⁻¹ ^ (n + 2)) <= qabs h * errorCoefficient C n := by
  let u := (x - pole)⁻¹
  let v := (x + h - pole)⁻¹
  let k := v - u
  let d : Rat := ((n + 1 : Nat) : Rat)
  let B := powerSecantErrorBound C (n + 1)
  have hC0 : 0 <= C := by grind
  have hB : 0 <= B := powerSecantErrorBound_nonneg hC0 _
  have hc1 : (x - pole) * u = 1 := Rat.mul_inv_cancel _ hx
  have hc2 : (x + h - pole) * v = 1 := Rat.mul_inv_cancel _ hxh
  have hhc := Rat.mul_inv_cancel h hh
  have hk : k = -h * u * v := by
    dsimp [k]
    grind
  have hkne : k ≠ 0 := by
    intro hz
    have huv : u * v = 0 := by grind
    have hu0 : u ≠ 0 := by grind
    have hv0 : v ≠ 0 := by grind
    grind [Rat.mul_eq_zero]
  have hkc := Rat.mul_inv_cancel k hkne
  have hpoint : u + k = v := by dsimp [k]; grind
  have he := qabs_normalized_power_differenceQuotient_sub_monomial_le
    (x := u) (h := k) hkne hC0 hC hu (by rw [hpoint]; exact hv) n
  rw [hpoint] at he
  change qabs ((v ^ (n + 1) / d - u ^ (n + 1) / d) / k - u ^ n) <= qabs k * B at he
  have hid :
      (primitive pole n (x + h) - primitive pole n x) / h - u ^ (n + 2) =
      u * v * ((v ^ (n + 1) / d - u ^ (n + 1) / d) / k - u ^ n) +
        u * k * u ^ n := by
    change (-(v ^ (n + 1) / d) - -(u ^ (n + 1) / d)) / h - u ^ (n + 2) = _
    have hchain : u * v * k⁻¹ = -h⁻¹ := by grind
    rw [show n + 2 = (n + 1) + 1 by omega, Rat.pow_succ, Rat.pow_succ]
    simp only [Rat.div_def]
    dsimp [k] at *
    grind
  rw [hid]
  have huv : qabs (u * v) <= C * C := by
    rw [qabs_mul]
    exact rat_mul_le_mul_of_nonneg (qabs_nonneg u) hu (qabs_nonneg v) hv
  have hkn : qabs k <= qabs h * (C * C) := by
    rw [hk, qabs_mul, qabs_mul, qabs_neg]
    have H := Rat.mul_le_mul_of_nonneg_left huv (qabs_nonneg h)
    simpa only [qabs_mul, Rat.mul_assoc] using H
  have hup : qabs (u ^ n) <= C ^ n := RationalMajorant.qabs_pow_le_pow hC0 hu n
  have hfirst : qabs (u * v * ((v ^ (n + 1) / d - u ^ (n + 1) / d) / k - u ^ n)) <=
      (C * C) * (qabs k * B) := by
    rw [qabs_mul]
    exact rat_mul_le_mul_of_nonneg (qabs_nonneg _) huv (qabs_nonneg _) he
  have hlast : qabs (u * k * u ^ n) <= (C * qabs k) * C ^ n := by
    rw [qabs_mul, qabs_mul]
    exact rat_mul_le_mul_of_nonneg (Rat.mul_nonneg (qabs_nonneg u) (qabs_nonneg k))
      (Rat.mul_le_mul_of_nonneg_right hu (qabs_nonneg k)) (qabs_nonneg _) hup
  have hs := Rat.le_trans (qabs_add_le _ _) (rat_add_le_add hfirst hlast)
  have hb : 0 <= C * C * B + C * C ^ n :=
    Rat.add_nonneg (Rat.mul_nonneg (Rat.mul_nonneg hC0 hC0) hB)
      (Rat.mul_nonneg hC0 (Rat.pow_nonneg hC0))
  have hbudget := Rat.mul_le_mul_of_nonneg_right hkn hb
  change qabs _ <= qabs h * ((C * C) * (C * C * B + C * C ^ n))
  grind

private theorem inverse_bound {y : Rat} {delta : QPos} (hy : delta.val <= qabs y) :
    qabs y⁻¹ <= delta.val⁻¹ := by
  have hyn : y ≠ 0 := by
    intro hz
    subst y
    have hp := delta.property
    have hzero : qabs (0 : Rat) = 0 := by decide +kernel
    rw [hzero] at hy
    grind
  have hc : qabs y * qabs y⁻¹ = 1 := by
    rw [← qabs_mul, Rat.mul_inv_cancel y hyn]
    exact qabs_eq_self_of_nonneg (by decide)
  have hd := Rat.mul_inv_cancel delta.val (Rat.ne_of_gt delta.property)
  have hs := Rat.mul_le_mul_of_nonneg_right hy (qabs_nonneg y⁻¹)
  apply Rat.le_of_mul_le_mul_left (c := delta.val)
  · grind
  · exact delta.property

/-- The inverse bound used by the algorithm is at least one. -/
def reciprocalBound (delta : QPos) : Rat := 1 + delta.val⁻¹

private theorem reciprocalBound_ge_one (delta : QPos) : 1 <= reciprocalBound delta := by
  have h := (Rat.inv_pos).2 delta.property
  unfold reciprocalBound
  grind

/-- Every repeated linear pole has a rational primitive on any explicitly
separated rational interval, with no sign assumption on the denominator. -/
def hasDerivative (pole a b : Rat) (delta : QPos)
    (hapart : ∀ x, inDomainInterval a b x → delta.val <= qabs (x - pole))
    (n : Nat) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (primitive pole n) a b)
      (FunctionOnInterval.exactRat (fun x => (x - pole)⁻¹ ^ (n + 2)) a b) := by
  let C := reciprocalBound delta
  let K := errorCoefficient C n
  have hC : 1 <= C := reciprocalBound_ge_one delta
  have hC0 : 0 <= C := by grind
  have hK : 0 <= K := errorCoefficient_nonneg hC0 n
  refine
    { same_lower := rfl
      same_upper := rfl
      stepPrecision := fun stage => 2 ^ RationalMajorant.halfDecayShift K (precisionAtStage stage)
      evalPrecision := fun _ _ _ => 0
      close := ?_ }
  intro x h stage hx hxh hdx hh hsmall
  have hxapart := hapart x hx
  have hyapart := hapart (x + h) hxh
  have hxn : x - pole ≠ 0 := by
    intro hz
    rw [hz, show qabs (0 : Rat) = 0 by decide +kernel] at hxapart
    have := delta.property
    grind
  have hyn : x + h - pole ≠ 0 := by
    intro hz
    rw [hz, show qabs (0 : Rat) = 0 by decide +kernel] at hyapart
    have := delta.property
    grind
  have hu : qabs (x - pole)⁻¹ <= C := by
    have hb := inverse_bound hxapart
    change qabs _ <= 1 + delta.val⁻¹
    grind
  have hv : qabs (x + h - pole)⁻¹ <= C := by
    have hb := inverse_bound hyapart
    change qabs _ <= 1 + delta.val⁻¹
    grind
  have he := secant_error hh hxn hyn hC hu hv n
  have hs := Rat.mul_le_mul_of_nonneg_right hsmall hK
  have ht := RationalMajorant.halfDecayShift_spec hK (precisionAtStage stage)
  rw [RationalMajorant.half_pow_eq_one_div_nat_two_pow] at ht
  have hbound : qabs ((primitive pole n (x + h) - primitive pole n x) / h -
      (x - pole)⁻¹ ^ (n + 2)) <= (precisionAtStage stage).val := by
    change qabs _ <= qabs h * K at he
    grind
  change intervalNearAtPrecision
    (QInterval.differenceQuotient
      {lo := primitive pole n (x + h), hi := primitive pole n (x + h)}
      {lo := primitive pole n x, hi := primitive pole n x} h)
    {lo := (x - pole)⁻¹ ^ (n + 2), hi := (x - pole)⁻¹ ^ (n + 2)} stage
  rw [QInterval.differenceQuotient_singleton]
  apply QInterval.nearAt_of_mem_mem_qabs_sub_le
    (x := (primitive pole n (x + h) - primitive pole n x) / h)
    (y := (x - pole)⁻¹ ^ (n + 2)) ⟨Rat.le_refl, Rat.le_refl⟩ ⟨Rat.le_refl, Rat.le_refl⟩ hbound
  · change _ - _ <= _
    rw [Rat.sub_self]
    exact Rat.le_of_lt (precisionAtStage stage).property
  · change _ - _ <= _
    rw [Rat.sub_self]
    exact Rat.le_of_lt (precisionAtStage stage).property


/-- Rational coefficients are handled by the automatic scaling rule. -/
def weighted_hasDerivative (c pole a b : Rat) (delta : QPos)
    (hapart : ∀ x, inDomainInterval a b x → delta.val <= qabs (x - pole))
    (n : Nat) := (hasDerivative pole a b delta hapart n).scale c

end RationalPrimitivePowers
end ComputableAnalysis
