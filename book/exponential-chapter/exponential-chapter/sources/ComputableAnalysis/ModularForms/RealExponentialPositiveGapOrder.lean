import ComputableAnalysis.ModularForms.RealMultiplicationValueOrder
import ComputableAnalysis.ModularForms.RealExponentialReality
import ComputableAnalysis.ModularForms.ExponentialAddition

/-! Actual exponential comparison across a justified positive represented real gap. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

/-- Adding a supplied positive represented real gap does not decrease the actual real exponential. -/
theorem entireExponential_real_positive_gap_order (x d : RealRaw) (hx : x.Valid) (hd : d.Valid)
    (hxp : x.Pos) (hdp : d.Pos) (hx0 : (RealRaw.ofRat 0).Le x) (hd0 : (RealRaw.ofRat 0).Le d) :
    (entireExponentialValue ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩).val.realPart.Le
      (entireExponentialValue (scalarSum ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩ ⟨ofRealRaw d,ofRealRaw_valid _ hd⟩)).val.realPart := by
  let X : Scalar := ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩
  let D : Scalar := ⟨ofRealRaw d,ofRealRaw_valid _ hd⟩
  let a := (entireExponentialValue X).val.realPart
  let b := (entireExponentialValue D).val.realPart
  have ha : a.Valid := realPart_valid (entireExponentialValue X).property
  have hb : b.Valid := realPart_valid (entireExponentialValue D).property
  have hla := entireExponential_real_rational_lower x hx hxp 0 hx0
  have hlb := entireExponential_real_rational_lower d hd hdp 0 hd0
  have h0a : (RealRaw.ofRat 0).Le a := by
    intro n m
    have h := hla 0 m
    change (1:Rat)+0≤(a.compute m).hi at h
    change (0:Rat)≤(a.compute m).hi
    grind only
  have h1b : (RealRaw.ofRat 1).Le b := by
    simpa only [Rat.add_zero] using hlb
  have hm := real_mul_ge_self_of_one_le a b ha hb h0a h1b
  have hea := entireExponential_real_embedding x hx
  have heb := entireExponential_real_embedding d hd
  have hprod := mul_equiv (entireExponentialValue X).property (ofRealRaw_valid _ ha)
    (entireExponentialValue D).property (ofRealRaw_valid _ hb) hea heb
  have he := equiv_trans (entireExponentialValue (scalarSum X D)).property
    (mul_valid (entireExponentialValue X).property (entireExponentialValue D).property)
    (ofRealRaw_valid _ (RealRaw.mul_valid ha hb)) (equiv_symm (entireExponential_addition X D))
    (equiv_trans (mul_valid (entireExponentialValue X).property (entireExponentialValue D).property)
      (mul_valid (ofRealRaw_valid _ ha) (ofRealRaw_valid _ hb))
      (ofRealRaw_valid _ (RealRaw.mul_valid ha hb)) hprod (real_embedding_mul a b ha hb))
  have hr := ComplexRaw.realPart_equiv (equiv_symm he)
  exact RealRaw.le_trans (RealRaw.mul_valid ha hb) hm
    (RealRaw.le_of_equiv (RealRaw.mul_valid ha hb)
      (realPart_valid (entireExponentialValue (scalarSum X D)).property) hr)

end ComputableAnalysis.ModularForms
