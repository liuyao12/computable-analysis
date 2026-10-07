import ComputableAnalysis.ModularForms.PairedRegularDivisionAgreement

/-! Uniform displacement bounds for the actual regular-series denominators. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedLiteralDenominator_difference (a z : Scalar) (t : Rat) :
    (sub (pairedLiteralDenominator z t).val (pairedLiteralDenominator a t).val).Equiv
      (mul (sub z.val a.val) (add z.val a.val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (pairedLiteralDenominator z t).property (pairedLiteralDenominator a t).property)
    (hright := mul_valid (sub_valid z.property a.property) (add_valid z.property a.property))
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let T := ComplexRawQuotient.ofQComplex ⟨t,0⟩
  change (Z*Z-T)-(A*A-T)=(Z-A)*(Z+A)
  grind only

theorem pairedLiteralDenominator_difference_bound (a z : Scalar)
    (ha : Small a.val (1/4)) (hz : Small z.val (1/4)) (t H : Rat)
    (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (sub (pairedLiteralDenominator z t).val (pairedLiteralDenominator a t).val) H := by
  have hs := LocalODE.small_add hz ha
  have hm := Small.mul (sub_valid z.property a.property) (add_valid z.property a.property)
    hH (show (0:Rat)≤1/4+1/4 by decide +kernel) hd hs
  have he : (2:Rat)*H*(1/4+1/4)=H := by grind only
  rw [he] at hm
  exact Small.congr (mul_valid (sub_valid z.property a.property) (add_valid z.property a.property))
    (sub_valid (pairedLiteralDenominator z t).property (pairedLiteralDenominator a t).property)
    (equiv_symm (pairedLiteralDenominator_difference a z t)) hm

end ComputableAnalysis.ModularForms
