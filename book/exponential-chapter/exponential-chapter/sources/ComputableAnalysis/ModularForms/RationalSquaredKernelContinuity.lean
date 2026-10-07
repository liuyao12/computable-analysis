import ComputableAnalysis.ModularForms.PairedRiccatiEdgePullbackAgreement
import ComputableAnalysis.ComplexReciprocalCalculus

/-! Quantitative rational squared-reciprocal continuity for contour refinement. -/
namespace ComputableAnalysis.ModularForms
open QComplex

theorem rationalSquare_difference_factor (z w : QComplex) :
    sub (mul z z) (mul w w)=mul (sub z w) (add z w) := by
  cases z
  cases w
  simp only [sub,add,neg,mul,QComplex.mk.injEq]
  constructor <;> grind only

theorem rationalSquaredInverse_difference_bound (z w : QComplex) (C margin : Rat)
    (hC : 0≤C) (hm : 0<margin)
    (hz : normBound z≤C) (hw : normBound w≤C)
    (hzm : margin≤normSq z) (hwm : margin≤normSq w) :
    normBound (sub (mul (inverse z) (inverse z)) (mul (inverse w) (inverse w)))≤
      2*(C*margin⁻¹)^3*normBound (sub z w) := by
  have hi := inverse_difference_normBound_le hC hm hz hw hzm hwm
  have hzI := inverse_normBound_le hC hm hz hzm
  have hwI := inverse_normBound_le hC hm hw hwm
  have hn : 0≤C*margin⁻¹ := Rat.mul_nonneg hC (Rat.le_of_lt (Rat.inv_pos.mpr hm))
  have hd := normBound_nonneg (sub z w)
  rw [rationalSquare_difference_factor]
  have hp := normBound_mul_le (sub (inverse z) (inverse w)) (add (inverse z) (inverse w))
  have ha := normBound_add_le (inverse z) (inverse w)
  have h1 := Rat.mul_le_mul_of_nonneg_right hi (normBound_nonneg (add (inverse z) (inverse w)))
  have h2 := Rat.mul_le_mul_of_nonneg_left
    (show normBound (add (inverse z) (inverse w))≤2*(C*margin⁻¹) by grind only)
    (Rat.mul_nonneg (Rat.mul_nonneg hn hn) hd)
  simp only [Rat.pow_succ,Rat.pow_zero,Rat.one_mul] at *
  grind only

end ComputableAnalysis.ModularForms
