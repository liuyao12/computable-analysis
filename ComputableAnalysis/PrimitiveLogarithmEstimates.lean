import ComputableAnalysis.ComplexLogarithmCompletedSecant

/-! Uniform finite estimates used by logarithm and arctangent primitives. -/
namespace ComputableAnalysis
namespace PrimitiveLogarithmEstimates
open ComplexLogarithmApproximation ComplexLogarithmJet ComplexLogarithmSecant

def half : Rat := 1/2

theorem half_nonneg : 0 ≤ half := by decide +kernel

theorem half_pow_antitone {k n : Nat} (h : k ≤ n) : half^n ≤ half^k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.add_succ, Rat.pow_succ]
    have hz := Rat.pow_nonneg half_nonneg (n := k+d)
    have hh : half ≤ 1 := by decide +kernel
    have ht := Rat.mul_le_mul_of_nonneg_left hh hz
    grind

theorem term_lipschitz {z w : QComplex}
    (hz : QComplex.normBound z ≤ half) (hw : QComplex.normBound w ≤ half) (n : Nat) :
    QComplex.normBound (QComplex.sub (term z n) (term w n)) ≤
      half^n * QComplex.normBound (QComplex.sub z w) := by
  have hpow := QComplex.pow_succ_difference_normBound_le half_nonneg hz hw n
  have hp : 0 < ((n+1 : Nat) : Rat) := Rat.natCast_pos.mpr (by omega)
  have hn := Rat.ne_of_gt hp
  have hi := Rat.le_of_lt (Rat.inv_pos.mpr hp)
  have hs : qabs (FormalPowerSeries.altSign n) = 1 := by
    unfold FormalPowerSeries.altSign
    split <;> decide +kernel
  have he : QComplex.sub (term z n) (term w n) =
      QComplex.scaleRat (FormalPowerSeries.altSign n / ((n+1 : Nat) : Rat))
        (QComplex.sub (QComplex.pow z (n+1)) (QComplex.pow w (n+1))) := by
    simp only [term, QComplex.sub, QComplex.add, QComplex.neg, QComplex.scaleRat,
      QComplex.divRat, Rat.div_def]
    congr 1 <;> grind
  rw [he, QComplex.normBound_scaleRat, Rat.div_def, qabs_mul, hs,
    qabs_eq_self_of_nonneg hi, Rat.one_mul]
  have h := Rat.mul_le_mul_of_nonneg_left hpow hi
  have hc := Rat.inv_mul_cancel _ hn
  simpa only [← Rat.mul_assoc, hc, Rat.one_mul] using h

theorem prefix_lipschitz_sum {z w : QComplex}
    (hz : QComplex.normBound z ≤ half) (hw : QComplex.normBound w ≤ half) (n : Nat) :
    QComplex.normBound (QComplex.sub (logPrefix z n) (logPrefix w n)) ≤
      RationalMajorant.geomTailPartial 1 half 0 n * QComplex.normBound (QComplex.sub z w) := by
  induction n with
  | zero =>
    change QComplex.normBound (QComplex.sub QComplex.zero QComplex.zero) ≤ 0 * _
    rw [Rat.zero_mul]
    decide +kernel
  | succ n ih =>
    have he : QComplex.sub (logPrefix z (n+1)) (logPrefix w (n+1)) =
        QComplex.add (QComplex.sub (logPrefix z n) (logPrefix w n))
          (QComplex.sub (term z n) (term w n)) := by
      simp only [logPrefix, tailPartial, Nat.zero_add, QComplex.sub, QComplex.add, QComplex.neg]
      congr 1 <;> grind
    rw [he]
    have h := Rat.le_trans (QComplex.normBound_add_le _ _)
      (rat_add_le_add ih (term_lipschitz hz hw n))
    simp only [RationalMajorant.geomTailPartial, Nat.zero_add, Rat.one_mul]
    grind

theorem prefix_lipschitz {z w : QComplex}
    (hz : QComplex.normBound z ≤ half) (hw : QComplex.normBound w ≤ half) (n : Nat) :
    QComplex.normBound (QComplex.sub (logPrefix z n) (logPrefix w n)) ≤
      2 * QComplex.normBound (QComplex.sub z w) := by
  have h := prefix_lipschitz_sum hz hw n
  have hg := RationalMajorant.geometric_tail_partial_bound
    (by decide +kernel : (0 : Rat) ≤ 1) half_nonneg (by decide +kernel : half ≤ 1/2) (N := 0) (k := n)
  have hg' : RationalMajorant.geomTailPartial 1 half 0 n ≤ 2 := by
    simpa [RationalMajorant.geomTailBound, half] using hg
  exact Rat.le_trans h (Rat.mul_le_mul_of_nonneg_right hg' (QComplex.normBound_nonneg _))

def kernel (m : QComplex) (t : Rat) : QComplex :=
  QComplex.mul m (QComplex.inverse (QComplex.add QComplex.one (QComplex.scaleRat t m)))

/-- The normalized logarithm's derivative changes continuously with its
computable coefficient, with an explicit rational bound. -/
theorem kernel_lipschitz {m p : QComplex} {t M r : Rat}
    (hm : QComplex.normBound m ≤ M) (hp : QComplex.normBound p ≤ M)
    (hM : 0 ≤ M) (hr : 0 ≤ r) (ht : qabs t ≤ r) (hMr : M*r ≤ half) :
    QComplex.normBound (QComplex.sub (kernel m t) (kernel p t)) ≤
      (8+64*M*r) * QComplex.normBound (QComplex.sub m p) := by
  have hmarg : QComplex.normBound (QComplex.scaleRat t m) ≤ half := by
    rw [QComplex.normBound_scaleRat]
    have h := Rat.mul_le_mul_of_nonneg_left hm (qabs_nonneg t)
    have h' := Rat.mul_le_mul_of_nonneg_right ht hM
    grind
  have hparg : QComplex.normBound (QComplex.scaleRat t p) ≤ half := by
    rw [QComplex.normBound_scaleRat]
    have h := Rat.mul_le_mul_of_nonneg_left hp (qabs_nonneg t)
    have h' := Rat.mul_le_mul_of_nonneg_right ht hM
    grind
  let a := QComplex.add QComplex.one (QComplex.scaleRat t m)
  let b := QComplex.add QComplex.one (QComplex.scaleRat t p)
  have ha := inverse_one_add_normBound_le_eight hmarg
  have hb := inverse_one_add_normBound_le_eight hparg
  have hi := QComplex.inverse_sub_inverse a b
    (one_add_normSq_ne_zero hmarg) (one_add_normSq_ne_zero hparg)
  have hdiff : QComplex.sub b a = QComplex.scaleRat (-t) (QComplex.sub m p) := by
    simp only [a, b, QComplex.sub, QComplex.add, QComplex.neg, QComplex.scaleRat, QComplex.one]
    congr 1 <;> grind
  have hnorm : QComplex.normBound (QComplex.sub b a) ≤ r * QComplex.normBound (QComplex.sub m p) := by
    rw [hdiff, QComplex.normBound_scaleRat, qabs_neg]
    exact Rat.mul_le_mul_of_nonneg_right ht (QComplex.normBound_nonneg _)
  have hiBound : QComplex.normBound (QComplex.sub (QComplex.inverse a) (QComplex.inverse b)) ≤
      64*r*QComplex.normBound (QComplex.sub m p) := by
    rw [hi]
    have h1 := QComplex.normBound_mul_le (QComplex.inverse a) (QComplex.sub b a)
    have h2 := QComplex.normBound_mul_le (QComplex.mul (QComplex.inverse a) (QComplex.sub b a)) (QComplex.inverse b)
    have h3 := Rat.mul_le_mul_of_nonneg_right ha (QComplex.normBound_nonneg (QComplex.sub b a))
    have h4 := Rat.mul_le_mul_of_nonneg_left hnorm (by decide +kernel : (0 : Rat) ≤ 8)
    have h5 := Rat.mul_le_mul_of_nonneg_left hb (QComplex.normBound_nonneg (QComplex.mul (QComplex.inverse a) (QComplex.sub b a)))
    grind
  have he : QComplex.sub (kernel m t) (kernel p t) =
      QComplex.add (QComplex.mul (QComplex.sub m p) (QComplex.inverse a))
        (QComplex.mul p (QComplex.sub (QComplex.inverse a) (QComplex.inverse b))) := by
    change QComplex.sub (QComplex.mul m (QComplex.inverse a)) (QComplex.mul p (QComplex.inverse b)) = _
    generalize QComplex.inverse a = u
    generalize QComplex.inverse b = v
    simp only [QComplex.sub, QComplex.add, QComplex.neg, QComplex.mul]
    congr 1 <;> grind
  rw [he]
  have h1 := QComplex.normBound_mul_le (QComplex.sub m p) (QComplex.inverse a)
  have h2 := QComplex.normBound_mul_le p (QComplex.sub (QComplex.inverse a) (QComplex.inverse b))
  have h3 := Rat.mul_le_mul_of_nonneg_left ha (QComplex.normBound_nonneg (QComplex.sub m p))
  have h4 := Rat.mul_le_mul_of_nonneg_right hp (QComplex.normBound_nonneg (QComplex.sub (QComplex.inverse a) (QComplex.inverse b)))
  have h5 := Rat.mul_le_mul_of_nonneg_left hiBound hM
  have h6 := QComplex.normBound_add_le
    (QComplex.mul (QComplex.sub m p) (QComplex.inverse a))
    (QComplex.mul p (QComplex.sub (QComplex.inverse a) (QComplex.inverse b)))
  grind

/-- Exact finite Taylor secants, uniformly in the logarithm coefficient. -/
theorem prefix_affine_secant {m : QComplex} {t h M : Rat}
    (hM : 0 ≤ M) (hm : QComplex.normBound m ≤ M)
    (ht : QComplex.normBound (QComplex.scaleRat t m) ≤ half)
    (hth : QComplex.normBound (QComplex.scaleRat (t+h) m) ≤ half)
    (hh : h ≠ 0) (n : Nat) :
    QComplex.normBound (QComplex.sub
      (QComplex.scaleRat h⁻¹ (QComplex.sub (logPrefix (QComplex.scaleRat (t+h) m) n)
        (logPrefix (QComplex.scaleRat t m) n))) (kernel m t)) ≤
      2*M*M*qabs h + 8*M*half^n := by
  let w := QComplex.scaleRat t m
  let v := QComplex.scaleRat h m
  have hv : QComplex.add w v = QComplex.scaleRat (t+h) m := by
    simp only [w, v, QComplex.add, QComplex.scaleRat]
    congr 1 <;> grind
  have hinc : QComplex.normBound v ≤ M*qabs h := by
    rw [QComplex.normBound_scaleRat]
    have H := Rat.mul_le_mul_of_nonneg_left hm (qabs_nonneg h)
    grind
  have hrem := prefixLinearRemainder_normBound_le_uniformHalfBall ht
    (by rw [hv]; exact hth) (Rat.mul_nonneg hM (qabs_nonneg h)) hinc n
  have hd := inverse_sub_derivativePrefix_normBound_le ht n
  have hdsym : QComplex.sub (derivativePrefix w n) (QComplex.inverse (QComplex.add QComplex.one w)) =
      QComplex.neg (QComplex.sub (QComplex.inverse (QComplex.add QComplex.one w)) (derivativePrefix w n)) := by
    simp only [QComplex.sub, QComplex.add, QComplex.neg]
    congr 1 <;> grind
  have hd' : QComplex.normBound (QComplex.sub (derivativePrefix w n)
      (QComplex.inverse (QComplex.add QComplex.one w))) ≤ 8*half^n := by
    rw [hdsym, QComplex.normBound_neg]
    exact hd
  have he : QComplex.sub
      (QComplex.scaleRat h⁻¹ (QComplex.sub (logPrefix (QComplex.scaleRat (t+h) m) n)
        (logPrefix w n))) (kernel m t) =
      QComplex.add (QComplex.scaleRat h⁻¹ (prefixLinearRemainder w v n))
        (QComplex.mul (QComplex.sub (derivativePrefix w n)
          (QComplex.inverse (QComplex.add QComplex.one w))) m) := by
    rw [← hv]
    unfold prefixLinearRemainder kernel
    change QComplex.sub (QComplex.scaleRat h⁻¹ (QComplex.sub (logPrefix (QComplex.add w v) n) (logPrefix w n)))
      (QComplex.mul m (QComplex.inverse (QComplex.add QComplex.one w))) = _
    generalize logPrefix (QComplex.add w v) n = A
    generalize logPrefix w n = B
    generalize derivativePrefix w n = D
    generalize QComplex.inverse (QComplex.add QComplex.one w) = E
    have hc := Rat.inv_mul_cancel h hh
    simp only [v, QComplex.sub, QComplex.add, QComplex.neg, QComplex.mul, QComplex.scaleRat]
    congr 1 <;> grind
  change QComplex.normBound _ ≤ _
  rw [he]
  have hs := Rat.mul_le_mul_of_nonneg_left hrem (qabs_nonneg h⁻¹)
  have hc : qabs h⁻¹ * qabs h = 1 := by
    rw [← qabs_mul, Rat.inv_mul_cancel h hh]
    decide +kernel
  have hr : QComplex.normBound (QComplex.scaleRat h⁻¹ (prefixLinearRemainder w v n)) ≤ 2*M*M*qabs h := by
    rw [QComplex.normBound_scaleRat]
    calc
      _ ≤ qabs h⁻¹ * (2 * (M*qabs h) * (M*qabs h)) := hs
      _ = 2*M*M*qabs h := by grind
  have h1 := QComplex.normBound_mul_le
    (QComplex.sub (derivativePrefix w n) (QComplex.inverse (QComplex.add QComplex.one w))) m
  have h2 := Rat.mul_le_mul_of_nonneg_right hd' (QComplex.normBound_nonneg m)
  have h3 := Rat.mul_le_mul_of_nonneg_left hm
    (Rat.mul_nonneg (by decide +kernel : (0 : Rat) ≤ 8) (Rat.pow_nonneg half_nonneg (n := n)))
  have h4 := QComplex.normBound_add_le
    (QComplex.scaleRat h⁻¹ (prefixLinearRemainder w v n))
    (QComplex.mul (QComplex.sub (derivativePrefix w n) (QComplex.inverse (QComplex.add QComplex.one w))) m)
  grind

end PrimitiveLogarithmEstimates
end ComputableAnalysis
