import ComputableAnalysis.ModularForms.CMOrderMap163

/-! Faithfulness of the concrete represented CM order map. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert
set_option maxRecDepth 8192

theorem integer_value_eq_zero (n : Int) (hn : (n : ScalarAlgebra.Value)=0) : n=0 := by
  have hc := (integer_constant n).trans hn
  have he := ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ComplexRaw.ofQComplex_valid ⟨(n:Rat),0⟩)
    (hright := ComplexRaw.ofQComplex_valid QComplex.zero) hc
  have ho := (ComplexRaw.compareAt_overlap_iff _ _ 0 0).mp (he 0)
  have hl : (n:Rat)≤0 := ho.1.1
  have hr : (0:Rat)≤(n:Rat) := ho.2.1
  have hrat : (n:Rat)=0 := Rat.le_antisymm hl hr
  exact_mod_cast hrat

namespace QuadraticOrder163

theorem complexValue_eq_zero_iff (u : QuadraticOrder163) : u.complexValue=0 ↔ u=zero := by
  constructor
  · intro hu
    have hn := u.complexValue_norm_product
    rw [hu] at hn
    have hz : (norm u : ScalarAlgebra.Value)=0 := by grind
    exact (norm_eq_zero_iff u).mp (integer_value_eq_zero _ hz)
  · intro hu
    rw [hu,complexValue_zero]

theorem complexValue_injective (u v : QuadraticOrder163)
    (h : u.complexValue=v.complexValue) : u=v := by
  have hs : (sub u v).complexValue=0 := by
    unfold sub
    rw [complexValue_add,complexValue_neg,h]
    grind
  exact (sub_eq_zero_iff u v).mp ((complexValue_eq_zero_iff _).mp hs)

theorem complexRaw_equiv_iff (u v : QuadraticOrder163) :
    u.complexRaw.Equiv v.complexRaw ↔ u=v := by
  constructor
  · intro h
    exact complexValue_injective u v (ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := u.complexRaw_valid) (hright := v.complexRaw_valid) h)
  · intro h
    rw [h]
    exact ComplexRaw.equiv_refl _ v.complexRaw_valid

end QuadraticOrder163
end ComputableAnalysis.ModularForms
