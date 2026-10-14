import ComputableAnalysis.RiemannHilbert.NonzeroBoxSearch
import ComputableAnalysis.RiemannHilbert.ScalarAlgebra

/-! Finite rational reciprocal arithmetic and bounds used by the executable
represented reciprocal. No represented inverse is assumed here. -/
namespace ComputableAnalysis.RiemannHilbert.RationalReciprocal
open ComplexRaw FunctionTheory BoxApproximation

def inverse (c : QComplex) : QComplex :=
  { re := c.re / QComplex.normSq c, im := -c.im / QComplex.normSq c }

theorem mul_inverse (c : QComplex) (hc : QComplex.normSq c ≠ 0) :
    QComplex.mul c (inverse c) = QComplex.one := by
  have h := QComplex.mul_inv?_eq_one hc
  simpa only [QComplex.inv?, if_neg hc, Option.map_some, inverse, Option.some.injEq] using h

theorem inverse_mul (c : QComplex) (hc : QComplex.normSq c ≠ 0) :
    QComplex.mul (inverse c) c = QComplex.one := by
  rw [QComplex.mul_comm_cert]
  exact mul_inverse c hc

theorem coordinateBound_inverse (c : QComplex) (C d : Rat)
    (hC : 0 ≤ C) (hd : 0 < d) (hcd : d ≤ QComplex.normSq c)
    (hc : coordinateBound c ≤ C) : coordinateBound (inverse c) ≤ C/d := by
  have hb := coordinateBound_bounds c
  have hn : 0 < QComplex.normSq c := by grind
  have hInv : 0 < (QComplex.normSq c)⁻¹ := (Rat.inv_pos).2 hn
  have hdi : 0 < d⁻¹ := (Rat.inv_pos).2 hd
  have hI : (QComplex.normSq c)⁻¹ ≤ d⁻¹ := by
    have hmul := Rat.mul_le_mul_of_nonneg_right hcd (Rat.le_of_lt hInv)
    have hmul2 := Rat.mul_le_mul_of_nonneg_left hmul (Rat.le_of_lt hdi)
    rw [Rat.mul_inv_cancel _ (Rat.ne_of_gt hn)] at hmul2
    rw [← Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt hd), Rat.one_mul, Rat.mul_one] at hmul2
    exact hmul2
  have hupper := Rat.mul_le_mul_of_nonneg_left hI hC
  have hlo := Rat.mul_le_mul_of_nonneg_right (show -C ≤ c.re by grind) (Rat.le_of_lt hInv)
  have hhi := Rat.mul_le_mul_of_nonneg_right (show c.re ≤ C by grind) (Rat.le_of_lt hInv)
  have hil := Rat.mul_le_mul_of_nonneg_right (show -C ≤ -c.im by grind) (Rat.le_of_lt hInv)
  have hih := Rat.mul_le_mul_of_nonneg_right (show -c.im ≤ C by grind) (Rat.le_of_lt hInv)
  unfold coordinateBound inverse qabs
  simp only [Rat.div_def]
  grind [Rat.neg_mul, Rat.mul_neg]

theorem raw_mul_constants (c d : QComplex) :
    (mul (ofQComplex c) (ofQComplex d)).Equiv (ofQComplex (QComplex.mul c d)) := by
  intro k
  apply (compareAt_overlap_iff _ _ k k).2
  apply QBox.overlaps_of_common_point (point := QComplex.mul c d)
  · exact QBox.mul_contains (QComplex.le_refl c) (QComplex.le_refl c)
      (QComplex.le_refl d) (QComplex.le_refl d)
  · exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩

theorem raw_inverse_mul (c : QComplex) (hc : QComplex.normSq c ≠ 0) :
    (mul (ofQComplex (inverse c)) (ofQComplex c)).Equiv (ofQComplex QComplex.one) := by
  have h := raw_mul_constants (inverse c) c
  rw [inverse_mul c hc] at h
  exact h

end ComputableAnalysis.RiemannHilbert.RationalReciprocal
