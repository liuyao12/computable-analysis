import ComputableAnalysis.ModularForms.PairedRegularDivisionZeroSum

/-! Exact reflection symmetry of the actual regular-division sum. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedRegularDivisionTerm_even (z w : Scalar) (hz : Small z.val (1/4))
    (hw : Small w.val (1/4)) (he : w.val.Equiv (neg z.val)) (n : Nat) :
    (pairedRegularDivisionTerm w hw n).val.Equiv (pairedRegularDivisionTerm z hz n).val := by
  have hs : (mul w.val w.val).Equiv (mul z.val z.val) := by
    have h := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := w.property) (hright := neg_valid z.property) he
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid w.property w.property) (hright := mul_valid z.property z.property)
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    let W := ComplexRawQuotient.ofRaw w.val w.property
    change W= -Z at h
    change W*W=Z*Z
    grind only
  exact scaleRat_equiv (RepresentedReciprocal.inverse_congr _ _ _ _
    (FunctionTheory.sub_congr hs (equiv_refl _ (ofQComplex_valid _))))

theorem pairedRegularDivisionValue_even (z w : Scalar) (hz : Small z.val (1/4))
    (hw : Small w.val (1/4)) (he : w.val.Equiv (neg z.val)) :
    (pairedRegularDivisionValue w hw).Equiv (pairedRegularDivisionValue z hz) :=
  inverseSquareSeriesValue_congr _ _
    (fun n => (pairedRegularDivisionTerm w hw n).property)
    (fun n => (pairedRegularDivisionTerm z hz n).property) 8
    (pairedRegularDivisionTerm_bound w hw) (pairedRegularDivisionTerm_bound z hz)
    (pairedRegularDivisionTerm_even z w hz hw he)

end ComputableAnalysis.ModularForms
