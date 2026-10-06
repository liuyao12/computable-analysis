import ComputableAnalysis.ModularForms.CMLatticeReciprocal163

/-! Explicit norm/conjugate reciprocal formula for CM lattice points. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163
open RiemannHilbert
set_option maxRecDepth 8192

def normInverseRaw (u : QuadraticOrder163) : ComplexRaw :=
  ComplexRaw.scaleRat ((norm u : Rat)⁻¹) (conjugate u).complexRaw

theorem normInverseRaw_valid (u : QuadraticOrder163) : u.normInverseRaw.Valid :=
  ComplexRaw.scaleRat_valid (conjugate u).complexRaw_valid

theorem normInverseRaw_product (u : QuadraticOrder163) (hu : u≠zero) :
    (ComplexRaw.mul u.complexRaw u.normInverseRaw).Equiv ComplexRaw.one := by
  have hn : (norm u : Rat)≠0 := by
    have hp := norm_positive u hu
    have hq : (0:Rat)<(norm u:Rat) := by exact_mod_cast hp
    exact Rat.ne_of_gt hq
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ComplexRaw.mul_valid u.complexRaw_valid u.normInverseRaw_valid)
    (hright := ComplexRaw.ofQComplex_valid QComplex.one)
  rw [ComplexRawQuotient.ofRaw_mul _ _ u.complexRaw_valid u.normInverseRaw_valid]
  change u.complexValue*ComplexRawQuotient.scaleRat ((norm u:Rat)⁻¹)
    (conjugate u).complexValue = (1:ScalarAlgebra.Value)
  rw [ComplexRawQuotient.mul_scaleRat,complexValue_norm_product]
  change ComplexRawQuotient.scaleRat ((norm u:Rat)⁻¹)
    (ComplexRawQuotient.scaleRat (norm u:Rat) 1)=1
  rw [ComplexRawQuotient.scaleRat_scaleRat]
  have hcancel : (norm u:Rat)⁻¹*(norm u:Rat)=1 := by
    rw [Rat.mul_comm]
    exact Rat.mul_inv_cancel _ hn
  rw [hcancel,ComplexRawQuotient.scaleRat_one]

theorem complexInverse_norm_formula (u : QuadraticOrder163) (hu : u≠zero) :
    (complexInverse u hu).val.Equiv u.normInverseRaw :=
  complexInverse_unique u hu ⟨u.normInverseRaw,u.normInverseRaw_valid⟩ (normInverseRaw_product u hu)

end ComputableAnalysis.ModularForms.QuadraticOrder163
