import ComputableAnalysis.ModularForms.CMPoint163
import ComputableAnalysis.ModularForms.RealComplexBridge
import ComputableAnalysis.ModularForms.ActionComposition

/-! The exact square-root equation inside represented complex algebra. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert
set_option maxRecDepth 8192

def sqrt163Complex : ComplexRaw := ComplexRaw.ofRealRaw sqrt163

theorem sqrt163Complex_valid : sqrt163Complex.Valid :=
  ComplexRaw.ofRealRaw_valid _ sqrt163_valid

theorem sqrt163Complex_square :
    (ComplexRaw.mul sqrt163Complex sqrt163Complex).Equiv
      (ComplexRaw.ofQComplex ⟨163,0⟩) := by
  have hmul := real_embedding_mul sqrt163 sqrt163 sqrt163_valid sqrt163_valid
  have he := ComplexRaw.ofRealRaw_equiv_of_equiv
    (x := RealRaw.mul sqrt163 sqrt163) (y := RealRaw.ofRat 163)
    (RealRaw.mul_valid sqrt163_valid sqrt163_valid) (RealRaw.ofRat_valid 163) sqrt163_square
  exact ComplexRaw.equiv_trans
    (ComplexRaw.mul_valid sqrt163Complex_valid sqrt163Complex_valid)
    (ComplexRaw.ofRealRaw_valid _ (RealRaw.mul_valid sqrt163_valid sqrt163_valid))
    (ComplexRaw.ofQComplex_valid _) hmul he

def sqrt163Value : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw sqrt163Complex sqrt163Complex_valid

theorem sqrt163Value_square : sqrt163Value*sqrt163Value=((163 : Int) : ScalarAlgebra.Value) := by
  have h := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ComplexRaw.mul_valid sqrt163Complex_valid sqrt163Complex_valid)
    (hright := ComplexRaw.ofQComplex_valid ⟨163,0⟩) sqrt163Complex_square
  rw [ComplexRawQuotient.ofRaw_mul] at h
  exact h.trans (integer_constant 163)

end ComputableAnalysis.ModularForms
