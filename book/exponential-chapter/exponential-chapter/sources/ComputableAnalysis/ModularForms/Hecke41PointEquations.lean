import ComputableAnalysis.ModularForms.Hecke41Points

/-! Exact matrix equations for the literal degree-41 point constructors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

private theorem scale_inverse_fortyOne (X : ScalarAlgebra.Value) :
    (41:ScalarAlgebra.Value)*ComplexRawQuotient.scaleRat (1/41) X=X := by
  have h : (41:ScalarAlgebra.Value)*ComplexRawQuotient.scaleRat (1/41) X=
      ComplexRawQuotient.scaleRat 41 (ComplexRawQuotient.scaleRat (1/41) X) := by
    rw [←show ((41:Nat):Rat)=(41:Rat) by decide +kernel,ScalarAlgebra.scale_natural 41]
    grind
  rw [h,ComplexRawQuotient.scaleRat_scaleRat,
    show (41:Rat)*(1/41)=1 by decide +kernel,ComplexRawQuotient.scaleRat_one]

/-- The literal represented point solves its determinant-41 matrix equation. -/
theorem hecke41Point_matrix_equation (i : Fin 42) (z : Scalar) :
    (mul (integerAffine (hecke41Representative i).c (hecke41Representative i).d z.val)
      (hecke41Point i z).val).Equiv
      (integerAffine (hecke41Representative i).a (hecke41Representative i).b z.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (integerAffine_valid _ _ z.property) (hecke41Point i z).property)
    (hright := integerAffine_valid _ _ z.property)
  change ComplexRawQuotient.ofRaw (integerAffine (hecke41Representative i).c (hecke41Representative i).d z.val)
      (integerAffine_valid _ _ z.property)*
    ComplexRawQuotient.ofRaw (hecke41Point i z).val (hecke41Point i z).property=
    ComplexRawQuotient.ofRaw (integerAffine (hecke41Representative i).a (hecke41Representative i).b z.val)
      (integerAffine_valid _ _ z.property)
  rw [integerAffine_class,integerAffine_class]
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  by_cases hi : i.val=41
  · simp only [hecke41Representative,hecke41Point,if_pos hi]
    have hs := ScalarAlgebra.scale_natural 41 Z
    rw [show ((41:Nat):Rat)=(41:Rat) by decide +kernel] at hs
    change (((0:Int):ScalarAlgebra.Value)*Z+((1:Int):ScalarAlgebra.Value))*
      ComplexRawQuotient.scaleRat 41 Z=((41:Int):ScalarAlgebra.Value)*Z+((0:Int):ScalarAlgebra.Value)
    grind
  · simp only [hecke41Representative,hecke41Point,if_neg hi]
    have hc := integer_constant (i.val:Int)
    rw [show ((i.val:Int):Rat)=(i.val:Rat) by exact_mod_cast (Eq.refl i.val)] at hc
    change (((0:Int):ScalarAlgebra.Value)*Z+((41:Int):ScalarAlgebra.Value))*
      ComplexRawQuotient.scaleRat (1/41) (Z+ComplexRawQuotient.ofQComplex ⟨(i.val:Rat),0⟩)=
        ((1:Int):ScalarAlgebra.Value)*Z+((i.val:Int):ScalarAlgebra.Value)
    have hs := scale_inverse_fortyOne (Z+ComplexRawQuotient.ofQComplex ⟨(i.val:Rat),0⟩)
    grind

/-- The representative denominators are the nonzero integer constants one or 41. -/
theorem hecke41Representative_denominator : ∀ i : Fin 42,
    (hecke41Representative i).c=0 ∧
      ((hecke41Representative i).d=1 ∨ (hecke41Representative i).d=41) := by
  decide +kernel

end ComputableAnalysis.ModularForms
