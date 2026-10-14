import ComputableAnalysis.ModularForms.CMRoot163

/-! Coordinate rotation agrees with multiplication in represented complex algebra. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert
set_option maxRecDepth 8192

def imaginaryUnitValue : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofQComplex ComplexRaw.imaginaryUnit

theorem mulI_class (z : Scalar) :
    ComplexRawQuotient.ofRaw (ComplexRaw.mulI z.val) (ComplexRaw.mulI_valid z.property) =
      imaginaryUnitValue*ComplexRawQuotient.ofRaw z.val z.property := by
  have he := ComplexRaw.qcomplexLeftMul_equiv_mul_ofQComplex
    ComplexRaw.imaginaryUnit z.property
  have h := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ComplexRaw.qcomplexLeftMul_valid _ z.property)
    (hright := ComplexRaw.mul_valid (ComplexRaw.ofQComplex_valid _) z.property) he
  change ComplexRawQuotient.scaleRat 0 (ComplexRawQuotient.ofRaw z.val z.property) +
    ComplexRawQuotient.scaleRat 1
      (ComplexRawQuotient.ofRaw (ComplexRaw.mulI z.val) (ComplexRaw.mulI_valid z.property)) =
    imaginaryUnitValue*ComplexRawQuotient.ofRaw z.val z.property at h
  rw [ComplexRawQuotient.scaleRat_zeroScalar,ComplexRawQuotient.scaleRat_one,
    ComplexRawQuotient.zero_add] at h
  exact h

theorem imaginaryUnitValue_square :
    imaginaryUnitValue*imaginaryUnitValue=(((-1):Int):ScalarAlgebra.Value) := by
  have he : (ComplexRaw.mul (ComplexRaw.ofQComplex ComplexRaw.imaginaryUnit)
      (ComplexRaw.ofQComplex ComplexRaw.imaginaryUnit)).Equiv
      (ComplexRaw.ofQComplex ⟨-1,0⟩) := by
    intro k
    apply (ComplexRaw.compareAt_overlap_iff _ _ k k).mpr
    simp only [ComplexRaw.mul,ComplexRaw.ofQComplex]
    decide +kernel
  have h := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ComplexRaw.mul_valid (ComplexRaw.ofQComplex_valid _) (ComplexRaw.ofQComplex_valid _))
    (hright := ComplexRaw.ofQComplex_valid _) he
  rw [ComplexRawQuotient.ofRaw_mul] at h
  exact h.trans (integer_constant (-1))

end ComputableAnalysis.ModularForms
