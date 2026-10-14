import ComputableAnalysis.ModularForms.CMConjugation163

/-! Complex conjugation and norm of every embedded order element. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert
set_option maxRecDepth 8192

theorem integerAffine_conjugate (a b : Int) (z : Scalar) :
    (ComplexRaw.conj (integerAffine a b z.val)).Equiv
      (integerAffine a b (ComplexRaw.conj z.val)) := by
  have he (n : Nat) : (ComplexRaw.conj (integerAffine a b z.val)).compute n=
      (integerAffine a b (ComplexRaw.conj z.val)).compute n := by
    simp only [ComplexRaw.conj,integerAffine,translate,ComplexRaw.add,
      ComplexRaw.ofQComplex,ComplexRaw.scaleRat,QBox.conj,QBox.scaleRat,QBox.add,QComplex.add]
    split <;> congr 1 <;> congr 1 <;> grind
  intro n
  apply (ComplexRaw.compareAt_overlap_iff _ _ n n).mpr
  rw [he]
  have ho := ComplexRaw.valid_ordered (integerAffine_valid a b
    (ComplexRaw.conj_valid _ z.property)) n
  exact ⟨⟨ho.1,ho.2⟩,⟨ho.1,ho.2⟩⟩

namespace QuadraticOrder163

theorem complexRaw_conjugate (u : QuadraticOrder163) :
    (ComplexRaw.conj u.complexRaw).Equiv (conjugate u).complexRaw := by
  have hfirst := integerAffine_conjugate u.y u.x (⟨cmPoint163,cmPoint163_valid⟩ : Scalar)
  have hsecond := integerAffine_equiv u.y u.x cmPoint163_conjugate
  have hlast : (integerAffine u.y u.x (integerAffine (-1) 1 cmPoint163)).Equiv
      (conjugate u).complexRaw := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := integerAffine_valid _ _ (integerAffine_valid (-1) 1 cmPoint163_valid))
      (hright := (conjugate u).complexRaw_valid)
    rw [integerAffine_class u.y u.x
      (⟨integerAffine (-1) 1 cmPoint163,integerAffine_valid (-1) 1 cmPoint163_valid⟩ : Scalar),
      integerAffine_class (-1) 1 (⟨cmPoint163,cmPoint163_valid⟩ : Scalar)]
    change (u.y : ScalarAlgebra.Value)*
      (((-1:Int):ScalarAlgebra.Value)*cmPoint163Value+((1:Int):ScalarAlgebra.Value))+
      (u.x : ScalarAlgebra.Value)=(conjugate u).complexValue
    rw [complexValue_formula]
    simp only [conjugate]
    grind
  exact ComplexRaw.equiv_trans (ComplexRaw.conj_valid _ u.complexRaw_valid)
    (integerAffine_valid _ _ (ComplexRaw.conj_valid _ cmPoint163_valid))
    (conjugate u).complexRaw_valid hfirst
    (ComplexRaw.equiv_trans (integerAffine_valid _ _ (ComplexRaw.conj_valid _ cmPoint163_valid))
      (integerAffine_valid _ _ (integerAffine_valid (-1) 1 cmPoint163_valid))
      (conjugate u).complexRaw_valid hsecond hlast)

theorem complexRaw_norm_product (u : QuadraticOrder163) :
    (ComplexRaw.mul u.complexRaw (ComplexRaw.conj u.complexRaw)).Equiv
      (ComplexRaw.ofQComplex ⟨(norm u : Rat),0⟩) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ComplexRaw.mul_valid u.complexRaw_valid (ComplexRaw.conj_valid _ u.complexRaw_valid))
    (hright := ComplexRaw.ofQComplex_valid _)
  rw [ComplexRawQuotient.ofRaw_mul _ _ u.complexRaw_valid
    (ComplexRaw.conj_valid _ u.complexRaw_valid)]
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ComplexRaw.conj_valid _ u.complexRaw_valid)
    (hright := (conjugate u).complexRaw_valid) (complexRaw_conjugate u)
  rw [he]
  exact (complexValue_norm_product u).trans (integer_constant (norm u)).symm

end QuadraticOrder163
end ComputableAnalysis.ModularForms
