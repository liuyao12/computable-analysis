import ComputableAnalysis.ModularForms.CMEquation163
import ComputableAnalysis.ModularForms.QuadraticDomain163

/-! Executable arithmetic-preserving map of the quadratic order at the CM point. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert
set_option maxRecDepth 8192

namespace QuadraticOrder163

def complexRaw (u : QuadraticOrder163) : ComplexRaw := integerAffine u.y u.x cmPoint163

theorem complexRaw_valid (u : QuadraticOrder163) : u.complexRaw.Valid :=
  integerAffine_valid _ _ cmPoint163_valid

def complexValue (u : QuadraticOrder163) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw u.complexRaw u.complexRaw_valid

theorem complexValue_formula (u : QuadraticOrder163) :
    u.complexValue=(u.x : ScalarAlgebra.Value)+(u.y : ScalarAlgebra.Value)*cmPoint163Value := by
  have h := integerAffine_class u.y u.x (⟨cmPoint163,cmPoint163_valid⟩ : Scalar)
  change u.complexValue=(u.y : ScalarAlgebra.Value)*cmPoint163Value+(u.x : ScalarAlgebra.Value) at h
  rw [h]
  grind

theorem complexValue_add (u v : QuadraticOrder163) :
    (add u v).complexValue=u.complexValue+v.complexValue := by
  rw [complexValue_formula,complexValue_formula,complexValue_formula]
  simp only [add]
  grind

theorem complexValue_mul (u v : QuadraticOrder163) :
    (mul u v).complexValue=u.complexValue*v.complexValue := by
  rw [complexValue_formula,complexValue_formula,complexValue_formula]
  simp only [mul]
  have h := cmPoint163Value_quadratic
  grind

theorem complexValue_zero : zero.complexValue=0 := by
  rw [complexValue_formula]
  simp only [zero]
  grind

theorem complexValue_one : one.complexValue=1 := by
  rw [complexValue_formula]
  simp only [one]
  grind

theorem complexValue_neg (u : QuadraticOrder163) :
    (neg u).complexValue= -u.complexValue := by
  rw [complexValue_formula,complexValue_formula]
  simp only [neg]
  grind

theorem complexValue_norm_product (u : QuadraticOrder163) :
    u.complexValue*(conjugate u).complexValue=(norm u : ScalarAlgebra.Value) := by
  rw [← complexValue_mul,mul_conjugate,complexValue_formula]
  grind

theorem complexRaw_add (u v : QuadraticOrder163) :
    (add u v).complexRaw.Equiv (ComplexRaw.add u.complexRaw v.complexRaw) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (add u v).complexRaw_valid)
    (hright := ComplexRaw.add_valid u.complexRaw_valid v.complexRaw_valid)
  rw [ComplexRawQuotient.ofRaw_add]
  exact complexValue_add u v

theorem complexRaw_mul (u v : QuadraticOrder163) :
    (mul u v).complexRaw.Equiv (ComplexRaw.mul u.complexRaw v.complexRaw) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (mul u v).complexRaw_valid)
    (hright := ComplexRaw.mul_valid u.complexRaw_valid v.complexRaw_valid)
  rw [ComplexRawQuotient.ofRaw_mul]
  exact complexValue_mul u v

end QuadraticOrder163
end ComputableAnalysis.ModularForms
