import ComputableAnalysis.ModularForms.LatticeHalfFrequencyRotationPower
import ComputableAnalysis.ModularForms.RotationQuarterPositivity

/-! A fourth root of unity in the upper half-plane is the imaginary unit.
Cancellation uses computed reciprocals, rather than an assumed field instance. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert
set_option maxHeartbeats 1000000

theorem upper_fourth_root_eq_imaginary_unit (z : Scalar)
    (hz : InUpperHalfPlane z.val)
    (hp : (LocalODE.power z.val 4).Equiv (ofQComplex QComplex.one)) :
    z.val.Equiv latticeImaginaryUnit.val := by
  let m := pairedMinus z ⟨one,ofQComplex_valid _⟩
  let p := pairedPlus z ⟨one,ofQComplex_valid _⟩
  let s := pairedPlus z latticeImaginaryUnit
  have hm : NonzeroBoxSearch.Nonzero m := upperShiftMinus_nonzero z hz 1
  have hpp : NonzeroBoxSearch.Nonzero p := upperShiftPlus_nonzero z hz 1
  have hs : NonzeroBoxSearch.Nonzero s := by
    apply upperScalar_nonzero
    obtain ⟨N,hN⟩ := hz
    refine ⟨N,?_⟩
    change 0 < (z.val.compute N).lo.im + 1
    change 0 < (z.val.compute N).lo.im at hN
    grind only
  have hmi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid m.property (RepresentedReciprocal.inverse m hm).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse m hm)
  have hpi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid p.property (RepresentedReciprocal.inverse p hpp).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse p hpp)
  have hsi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid s.property (RepresentedReciprocal.inverse s hs).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse s hs)
  have hpow := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := LocalODE.power_valid z.val z.property 4)
    (hright := ofQComplex_valid _) hp
  let Z := gridScalarValue z
  let I := gridScalarValue latticeImaginaryUnit
  let M := gridScalarValue (RepresentedReciprocal.inverse m hm)
  let P := gridScalarValue (RepresentedReciprocal.inverse p hpp)
  let S := gridScalarValue (RepresentedReciprocal.inverse s hs)
  change (Z + -1)*M=1 at hmi
  change (Z+1)*P=1 at hpi
  change (Z+I)*S=1 at hsi
  change (((1*Z)*Z)*Z)*Z=1 at hpow
  have hi : I*I = -1 := latticeImaginaryUnit_square
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := z.property)
    (hright := latticeImaginaryUnit.property)
  change Z=I
  have hf : ((Z + -1)*(Z+1)*(Z+ -I))*(Z+I)=0 := by grind only
  have hc : Z+ -I=0 := by grind only
  grind only

theorem latticeHalfFrequency_rotation_imaginary_unit :
    (RotationLift.HalfPiInput.rotation latticeHalfFrequencyRotationInput).Equiv
      latticeImaginaryUnit.val :=
  upper_fourth_root_eq_imaginary_unit
    ⟨_,RotationLift.HalfPiInput.rotation_valid latticeHalfFrequencyRotationInput⟩
    (rotationQuarter_represented_positive latticeHalfFrequencyRotationInput)
    latticeHalfFrequency_rotation_fourth_one

end ComputableAnalysis.ModularForms
