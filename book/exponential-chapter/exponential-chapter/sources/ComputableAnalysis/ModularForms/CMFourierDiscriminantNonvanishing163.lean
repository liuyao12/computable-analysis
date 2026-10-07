import ComputableAnalysis.ModularForms.CMExponentialUpperBound163
import ComputableAnalysis.ModularForms.NomeFourierChoiceAgreement

/-! Concrete nonvanishing of the actual CM Fourier discriminant from proved exponential bounds. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem inverse_cancel_order (B U V : Rat) (hb : B*V=1) (h : V*1≤V*(B*U)) : V≤U := by
  rw [Rat.mul_one, ← Rat.mul_assoc, Rat.mul_comm V B, hb, Rat.one_mul] at h
  exact h

/-- A justified upper bound on a positive represented value gives the reciprocal lower bound. -/
theorem positiveReciprocal_lower_of_upper (x : RealRaw) (hx : x.Valid) (l B : Rat)
    (hlpos : 0<l) (hBpos : 0<B) (hlB : l≤B)
    (hl : (RealRaw.ofRat l).Le x) (hu : x.Le (RealRaw.ofRat B)) :
    (RealRaw.ofRat (1/B)).Le (RealRaw.positiveReciprocal x l) := by
  intro n m
  rw [RealRaw.positiveReciprocal_compute x l hlpos m]
  change 1/B≤1/maxRat2 (x.compute m).lo l
  have hupper := hu m 0
  change (x.compute m).lo≤B at hupper
  have hmax : maxRat2 (x.compute m).lo l≤B := by
    unfold maxRat2
    split <;> assumption
  have hpos : 0<maxRat2 (x.compute m).lo l := by
    unfold maxRat2
    split <;> grind only
  have hi := Rat.mul_inv_cancel (maxRat2 (x.compute m).lo l) (Rat.ne_of_gt hpos)
  have hb := Rat.mul_inv_cancel B (Rat.ne_of_gt hBpos)
  have h1 := Rat.mul_le_mul_of_nonneg_right hmax (Rat.le_of_lt (Rat.inv_pos.mpr hpos))
  rw [hi] at h1
  have h2 := Rat.mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt (Rat.inv_pos.mpr hBpos))
  rw [Rat.div_def,Rat.div_def,Rat.one_mul,Rat.one_mul]
  exact inverse_cancel_order B (maxRat2 (x.compute m).lo l)⁻¹ B⁻¹ hb h2

/-- The actual CM nome magnitude has a justified positive rational lower bound. -/
theorem cmNomeMagnitude163_lower_power :
    (RealRaw.ofRat (1/((8:Rat)^26))).Le cmNomeMagnitude163 :=
  positiveReciprocal_lower_of_upper cmGrowthValue163
    (realPart_valid (entireExponentialValue cmGrowthExponent163).property) 25 ((8:Rat)^26)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    cmGrowthExponential163_lower_twentyFive cmGrowthExponential163_upper_power

/-- The actual CM nome is separated from the certified Fourier discriminant error. -/
theorem nome_cm163_not_small_discriminant_error :
    ¬Small (nome.eval cmScalar163 cmPoint163_upper).val
      (9000*(1/140737488355328)*(1/140737488355328)) := by
  intro hs
  let E : Rat := 9000*(1/140737488355328)*(1/140737488355328)
  have h := Small.congr (nome.eval cmScalar163 cmPoint163_upper).property
    (neg_valid (ofRealRaw_valid _ cmNomeMagnitude163_valid)) nome_cm163_reciprocal hs
  have hu : cmNomeMagnitude163.Le (RealRaw.ofRat E) := by
    intro n m
    have hl := h.1 0 n
    change -E≤ -(cmNomeMagnitude163.compute n).lo at hl
    change (cmNomeMagnitude163.compute n).lo≤E
    grind only
  have hr := RealRaw.le_trans cmNomeMagnitude163_valid cmNomeMagnitude163_lower_power hu
  have hbad := hr 0 0
  change 1/((8:Rat)^26)≤E at hbad
  have hgood : E<1/((8:Rat)^26) := by decide +kernel
  grind only

/-- The constructed Fourier discriminant at the actual CM point is nonzero. -/
theorem cmFourierDiscriminant163_nonzero : NonzeroBoxSearch.Nonzero cmFourierDiscriminant163 :=
  scalar_nonzero_of_small_difference cmFourierDiscriminant163 (nome.eval cmScalar163 cmPoint163_upper) _
    cmFourierDiscriminant163_nome_bound_fortySeven nome_cm163_not_small_discriminant_error

end ComputableAnalysis.ModularForms
