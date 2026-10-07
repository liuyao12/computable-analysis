import ComputableAnalysis.ModularForms.PairedUpperDomain

/-! An actual upper-half-plane scalar cannot be a square root of one.
The factor cancellation uses constructed reciprocals. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

private def squareScalarValue (z : Scalar) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw z.val z.property

theorem upper_square_ne_one (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ¬ (LocalODE.power z.val 2).Equiv one := by
  intro hp
  let m := pairedMinus z ⟨one,ofQComplex_valid _⟩
  let p := pairedPlus z ⟨one,ofQComplex_valid _⟩
  have hm : NonzeroBoxSearch.Nonzero m := upperShiftMinus_nonzero z hz 1
  have hpp : NonzeroBoxSearch.Nonzero p := upperShiftPlus_nonzero z hz 1
  let mi := RepresentedReciprocal.inverse m hm
  let pi := RepresentedReciprocal.inverse p hpp
  have hM := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid m.property mi.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse m hm)
  have hP := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid p.property pi.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse p hpp)
  have hZ := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := LocalODE.power_valid z.val z.property 2) (hright := ofQComplex_valid _) hp
  let Z := squareScalarValue z
  let M := squareScalarValue mi
  let P := squareScalarValue pi
  change (Z+ -1)*M=1 at hM
  change (Z+1)*P=1 at hP
  change (1*Z)*Z=1 at hZ
  have hbad : (1:ScalarAlgebra.Value)=0 := by grind only
  have he : one.Equiv zero := ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ofQComplex_valid _) (hright := ofQComplex_valid _) hbad
  have h := (compareAt_overlap_iff _ _ 0 0).mp (he 0)
  change ((1:Rat)≤0 ∧ (0:Rat)≤0) ∧ ((0:Rat)≤1 ∧ (0:Rat)≤0) at h
  grind only

end ComputableAnalysis.ModularForms
