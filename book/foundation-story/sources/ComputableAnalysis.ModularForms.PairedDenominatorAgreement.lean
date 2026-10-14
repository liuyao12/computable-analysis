import ComputableAnalysis.ModularForms.PairedRescaledInverse

/-! Exact agreement of rescaled and literal paired denominators. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem rationalScalarOne_equiv (t : Rat) :
    (scaleRat t (ofQComplex QComplex.one)).Equiv (ofQComplex ⟨t,0⟩) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  by_cases ht : 0≤t <;>
    simp [scaleRat,ofQComplex,QBox.scaleRat,QComplex.one,ht,QBox.Overlaps]

theorem pairedDenominator_rescaling (z : Scalar) (c t : Rat) (hct : t*c=1) :
    (scaleRat (-t) (nomeDenominator (pairedNormalizedSquare z c)).val).Equiv
      (sub (mul z.val z.val) (ofQComplex ⟨t,0⟩)) := by
  have vx := mul_valid z.property z.property
  have hr := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := scaleRat_valid (ofQComplex_valid QComplex.one)) (hright := ofQComplex_valid ⟨t,0⟩)
    (rationalScalarOne_equiv t)
  rw [ComplexRawQuotient.ofRaw_scaleRat _ _ (ofQComplex_valid QComplex.one)] at hr
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := scaleRat_valid (nomeDenominator (pairedNormalizedSquare z c)).property)
    (hright := sub_valid vx (ofQComplex_valid _))
  let X := ComplexRawQuotient.ofRaw (mul z.val z.val) vx
  change ComplexRawQuotient.scaleRat (-t) (1 + -(ComplexRawQuotient.scaleRat c X)) =
    X + -(ComplexRawQuotient.ofQComplex ⟨t,0⟩)
  rw [ComplexRawQuotient.scaleRat_add]
  have hn (a : Rat) (Y : ScalarAlgebra.Value) :
      ComplexRawQuotient.scaleRat (-a) Y = -(ComplexRawQuotient.scaleRat a Y) := by
    rw [← ComplexRawQuotient.neg_scaleRat]
  change ComplexRawQuotient.scaleRat t 1=ComplexRawQuotient.ofQComplex ⟨t,0⟩ at hr
  rw [hn t,← hr]
  rw [ComplexRawQuotient.neg_scaleRat c X,ComplexRawQuotient.scaleRat_scaleRat]
  rw [show (-t)*(-c)=1 by grind only,ComplexRawQuotient.scaleRat_one]
  grind only

end ComputableAnalysis.ModularForms
