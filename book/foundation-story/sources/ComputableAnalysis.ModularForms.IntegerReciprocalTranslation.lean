import ComputableAnalysis.ModularForms.PairedUpperDomain
import ComputableAnalysis.ModularForms.ActionComposition
import ComputableAnalysis.ModularForms.SymmetricLatticeShift

/-! Integer-indexed actual reciprocal families for symmetric lattice translation. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def integerShiftScalar (z : Scalar) (k : Int) : Scalar :=
  ⟨integerAffine 1 k z.val,integerAffine_valid _ _ z.property⟩

theorem integerShiftScalar_upper (z : Scalar) (hz : InUpperHalfPlane z.val) (k : Int) :
    InUpperHalfPlane (integerShiftScalar z k).val := by
  obtain ⟨N,hN⟩ := hz
  change 0<(z.val.compute N).lo.im at hN
  refine ⟨N,?_⟩
  simpa only [integerShiftScalar,integerAffine,translate,scaleRat,QBox.scaleRat,
    imagPart,add, Rat.intCast_one,
    if_pos (show (0:Rat)≤1 by decide),ofQComplex,QBox.add,QComplex.add,
    Rat.mul_one,Rat.one_mul,Rat.add_zero] using hN

theorem integerShiftScalar_composition (z : Scalar) (j k : Int) :
    (integerShiftScalar (integerShiftScalar z j) k).val.Equiv (integerShiftScalar z (j+k)).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (integerShiftScalar (integerShiftScalar z j) k).property)
    (hright := (integerShiftScalar z (j+k)).property)
  change ComplexRawQuotient.ofRaw (integerAffine 1 k (integerShiftScalar z j).val) _ =
    ComplexRawQuotient.ofRaw (integerAffine 1 (j+k) z.val) _
  rw [integerAffine_class,integerAffine_class]
  simp only [integerShiftScalar, integerAffine_class]
  grind only

def upperIntegerReciprocal (z : Scalar) (hz : InUpperHalfPlane z.val) (k : Int) : Scalar :=
  RepresentedReciprocal.inverse (integerShiftScalar z k)
    (upperScalar_nonzero _ (integerShiftScalar_upper z hz k))

theorem upperIntegerReciprocal_translation (z : Scalar) (hz : InUpperHalfPlane z.val) (j k : Int) :
    (upperIntegerReciprocal (integerShiftScalar z j) (integerShiftScalar_upper z hz j) k).val.Equiv
      (upperIntegerReciprocal z hz (j+k)).val :=
  RepresentedReciprocal.inverse_congr _ _ _ _ (integerShiftScalar_composition z j k)

def upperIntegerReciprocalClass (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k : Int) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw (upperIntegerReciprocal z hz k).val
    (upperIntegerReciprocal z hz k).property

theorem upperIntegerReciprocalClass_translation (z : Scalar)
    (hz : InUpperHalfPlane z.val) (j k : Int) :
    upperIntegerReciprocalClass (integerShiftScalar z j)
      (integerShiftScalar_upper z hz j) k = upperIntegerReciprocalClass z hz (j+k) :=
  ComplexRawQuotient.ofRaw_eq_ofRaw (upperIntegerReciprocal_translation z hz j k)

theorem upperIntegerReciprocal_symmetric_shift (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) :
    symmetricLatticeSum (upperIntegerReciprocalClass (integerShiftScalar z 1)
      (integerShiftScalar_upper z hz 1)) N -
      symmetricLatticeSum (upperIntegerReciprocalClass z hz) N =
    upperIntegerReciprocalClass z hz ((N:Int)+1) -
      upperIntegerReciprocalClass z hz (-(N:Int)) := by
  have hf : upperIntegerReciprocalClass (integerShiftScalar z 1)
      (integerShiftScalar_upper z hz 1) =
      (fun k => upperIntegerReciprocalClass z hz (k+1)) := by
    funext k
    rw [upperIntegerReciprocalClass_translation z hz 1 k]
    congr 1
    omega
  rw [hf]
  exact symmetricLatticeSum_shift _ N

end ComputableAnalysis.ModularForms
