import ComputableAnalysis.ModularForms.PairedRegularDivisionDerivative
import ComputableAnalysis.ModularForms.PairedRegularDivisionEven

/-! Exact reflection symmetry for actual regular-division derivative terms. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedSmallDiskLiteralInverseMap_even (n : Nat) (z w : Scalar)
    (hz : LocalODE.interior (1/4) z) (hw : LocalODE.interior (1/4) w)
    (he : w.val.Equiv (neg z.val)) :
    ((pairedSmallDiskLiteralInverseMap n).eval w hw).val.Equiv
      ((pairedSmallDiskLiteralInverseMap n).eval z hz).val := by
  have hs : (mul w.val w.val).Equiv (mul z.val z.val) := by
    have h := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := w.property) (hright := neg_valid z.property) he
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid w.property w.property) (hright := mul_valid z.property z.property)
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    let W := ComplexRawQuotient.ofRaw w.val w.property
    change W= -Z at h
    change W*W=Z*Z
    grind only
  exact RepresentedReciprocal.inverse_congr _ _ _ _
    (FunctionTheory.sub_congr hs (equiv_refl _ (ofQComplex_valid _)))

theorem pairedRegularDivisionDerivativeTerm_odd (n : Nat) (z w : Scalar)
    (hz : LocalODE.interior (1/4) z) (hw : LocalODE.interior (1/4) w)
    (he : w.val.Equiv (neg z.val)) :
    (pairedRegularDivisionDerivativeTerm w hw n).val.Equiv
      (neg (pairedRegularDivisionDerivativeTerm z hz n).val) := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((pairedSmallDiskLiteralInverseMap n).eval w hw).property)
    (hright := ((pairedSmallDiskLiteralInverseMap n).eval z hz).property)
    (pairedSmallDiskLiteralInverseMap_even n z w hz hw he)
  have h := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := w.property) (hright := neg_valid z.property) he
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedRegularDivisionDerivativeTerm w hw n).property)
    (hright := neg_valid (pairedRegularDivisionDerivativeTerm z hz n).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let W := ComplexRawQuotient.ofRaw w.val w.property
  let I := ComplexRawQuotient.ofRaw ((pairedSmallDiskLiteralInverseMap n).eval z hz).val
    ((pairedSmallDiskLiteralInverseMap n).eval z hz).property
  let J := ComplexRawQuotient.ofRaw ((pairedSmallDiskLiteralInverseMap n).eval w hw).val
    ((pairedSmallDiskLiteralInverseMap n).eval w hw).property
  change J=I at hi
  change W= -Z at h
  change (-(J*J)*(W+W))+(-(J*J)*(W+W))= -((-(I*I)*(Z+Z))+(-(I*I)*(Z+Z)))
  grind only

end ComputableAnalysis.ModularForms
