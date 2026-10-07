import ComputableAnalysis.ComplexReciprocalCalculus

namespace ComputableAnalysis.PolynomialDescentDomain

/-- Coordinate margins imply retention of the whole rational displacement
ball. This is a finite domain lemma, independent of root existence. -/
theorem displacement_in_box (box : QBox) (x h : QComplex) (radius : Rat)
    (hlre : box.lo.re + radius ≤ x.re) (hhre : x.re + radius ≤ box.hi.re)
    (hlim : box.lo.im + radius ≤ x.im) (hhim : x.im + radius ≤ box.hi.im)
    (hsmall : QComplex.normBound h ≤ radius) :
    box.lo ≤ QComplex.add x h ∧ QComplex.add x h ≤ box.hi := by
  have hrlo := neg_qabs_le_self h.re
  have hrhi := self_le_qabs h.re
  have hilo := neg_qabs_le_self h.im
  have hihi := self_le_qabs h.im
  have hr := qabs_nonneg h.re
  have hi := qabs_nonneg h.im
  simp only [QComplex.normBound, QComplex.add, QComplex.le_def] at *
  constructor <;> constructor <;> grind

def safeStep (radius : QPos) (direction : QComplex) : Rat :=
  radius.val / (QComplex.normBound direction + radius.val + 1)

/-- A computed positive step stays below one and fits the direction inside
the supplied domain margin. No normalizing square root is needed. -/
theorem safeStep_spec (radius : QPos) (direction : QComplex) :
    0 < safeStep radius direction ∧ safeStep radius direction < 1 ∧
      QComplex.normBound (QComplex.scaleRat (safeStep radius direction) direction) ≤ radius.val := by
  have hn := QComplex.normBound_nonneg direction
  have hr := radius.property
  have hden : 0 < QComplex.normBound direction + radius.val + 1 := by grind
  have hi := Rat.inv_pos.mpr hden
  have hc := Rat.mul_inv_cancel (QComplex.normBound direction + radius.val + 1) (Rat.ne_of_gt hden)
  have ht : 0 < safeStep radius direction := by
    unfold safeStep
    rw [Rat.div_def]
    exact Rat.mul_pos hr hi
  have hlt := Rat.mul_lt_mul_of_pos_right
    (show radius.val < QComplex.normBound direction + radius.val + 1 by grind) hi
  have hprod := Rat.mul_nonneg (Rat.le_of_lt hr) (Rat.le_of_lt hi)
  have hbound := Rat.mul_le_mul_of_nonneg_right
    (show QComplex.normBound direction ≤ QComplex.normBound direction + radius.val + 1 by grind) hprod
  refine ⟨ht, ?_, ?_⟩
  · unfold safeStep
    rw [Rat.div_def]
    grind
  · rw [QComplex.normBound_scaleRat, qabs_eq_self_of_nonneg (Rat.le_of_lt ht)]
    have heq : (QComplex.normBound direction + radius.val + 1) *
        (radius.val * (QComplex.normBound direction + radius.val + 1)⁻¹) = radius.val := by
      grind
    rw [heq] at hbound
    unfold safeStep
    rw [Rat.div_def]
    grind

end ComputableAnalysis.PolynomialDescentDomain
