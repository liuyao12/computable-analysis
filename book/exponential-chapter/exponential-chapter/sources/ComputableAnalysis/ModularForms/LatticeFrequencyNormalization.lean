import ComputableAnalysis.ModularForms.LatticeFrequencyInput
import ComputableAnalysis.ModularForms.ContinuedLatticeReciprocalAgreement

/-! Exact frequency normalization of the actual lattice reciprocal equation. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
noncomputable section

theorem latticeFrequencySquare_embedding_neg :
    ofRealRaw latticeFrequencySquare=neg (ofRealRaw pairedRiccatiCenterConstant.val.realPart) := by
  change ofRealRaw (RealRaw.neg pairedRiccatiCenterConstant.val.realPart)=neg (ofRealRaw pairedRiccatiCenterConstant.val.realPart)
  simp only [ofRealRaw,RealRaw.neg,RealRaw.negCompute,
    neg,QBox.neg,QComplex.neg,Rat.neg_zero]

theorem latticeFrequency_complex_square_identity :
    (mul latticeFrequency.val latticeFrequency.val).Equiv (neg pairedRiccatiCenterConstant.val) := by
  have he := latticeFrequency_square_identity
  rw [latticeFrequencySquare_embedding_neg] at he
  exact equiv_trans (mul_valid latticeFrequency.property latticeFrequency.property)
    (neg_valid (ofRealRaw_valid _ (realPart_valid pairedRiccatiCenterConstant.property)))
    (neg_valid pairedRiccatiCenterConstant.property) he
    (ComplexRaw.neg_equiv (equiv_symm latticeRiccatiConstant_real_embedding))

def normalizedLatticeTangentMap : DomainFunctions.Map :=
  compose (affine ⟨zero,ofQComplex_valid _⟩ latticeFrequency) continuedLatticeReciprocalMap

def normalizedLatticeTangentMap_holomorphic : Holomorphic normalizedLatticeTangentMap :=
  (affine_holomorphic ⟨zero,ofQComplex_valid _⟩ latticeFrequency).compose
    continuedLatticeReciprocalMap_holomorphic

theorem normalizedLatticeTangent_differential_identity (z : Scalar)
    (hz : normalizedLatticeTangentMap.domain z) :
    (normalizedLatticeTangentMap_holomorphic.derivative z hz).val.Equiv
      (mul latticeFrequency.val (add (ofQComplex QComplex.one)
        (mul (normalizedLatticeTangentMap.eval z hz).val
          (normalizedLatticeTangentMap.eval z hz).val))) := by
  let hw := compose_inner_mem hz
  let w := continuedLatticeReciprocalMap.eval z hw
  let d := continuedLatticeReciprocalMap_holomorphic.derivative z hw
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := d.property)
    (hright := sub_valid (ofQComplex_valid _)
      (mul_valid pairedRiccatiCenterConstant.property (mul_valid w.property w.property)))
    (continuedLatticeReciprocal_differential_identity z hw)
  have ha := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid latticeFrequency.property latticeFrequency.property)
    (hright := neg_valid pairedRiccatiCenterConstant.property) latticeFrequency_complex_square_identity
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (normalizedLatticeTangentMap_holomorphic.derivative z hz).property)
    (hright := mul_valid latticeFrequency.property (add_valid (ofQComplex_valid _)
      (mul_valid (normalizedLatticeTangentMap.eval z hz).property
        (normalizedLatticeTangentMap.eval z hz).property)))
  let W := gridScalarValue w
  let D := gridScalarValue d
  let C := gridScalarValue pairedRiccatiCenterConstant
  let A := gridScalarValue latticeFrequency
  change D=1-C*(W*W) at hd
  change A*A= -C at ha
  change A*D=A*(1+(0+A*W)*(0+A*W))
  rw [hd]
  grind only

theorem normalizedLatticeTangent_center_mem (z : Scalar) (he : z.val.Equiv zero) :
    normalizedLatticeTangentMap.domain z := ⟨continuedLatticeReciprocal_center_mem z he,trivial⟩

theorem normalizedLatticeTangent_center_zero (z : Scalar) (he : z.val.Equiv zero) :
    (normalizedLatticeTangentMap.eval z (normalizedLatticeTangent_center_mem z he)).val.Equiv zero := by
  let hw := continuedLatticeReciprocal_center_mem z he
  have hh := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (continuedLatticeReciprocalMap.eval z hw).property) (hright := ofQComplex_valid _)
    (continuedLatticeReciprocal_center_zero z he)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (normalizedLatticeTangentMap.eval z (normalizedLatticeTangent_center_mem z he)).property)
    (hright := ofQComplex_valid _)
  let W := gridScalarValue (continuedLatticeReciprocalMap.eval z hw)
  let A := gridScalarValue latticeFrequency
  change W=0 at hh
  change 0+A*W=0
  rw [hh]
  grind only

theorem normalizedLatticeTangent_center_derivative (z : Scalar) (he : z.val.Equiv zero) :
    (normalizedLatticeTangentMap_holomorphic.derivative z
      (normalizedLatticeTangent_center_mem z he)).val.Equiv latticeFrequency.val := by
  let hz := normalizedLatticeTangent_center_mem z he
  let u := normalizedLatticeTangentMap.eval z hz
  let d := normalizedLatticeTangentMap_holomorphic.derivative z hz
  have hu := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := u.property) (hright := ofQComplex_valid _)
    (normalizedLatticeTangent_center_zero z he)
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := d.property)
    (hright := mul_valid latticeFrequency.property (add_valid (ofQComplex_valid _) (mul_valid u.property u.property)))
    (normalizedLatticeTangent_differential_identity z hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := d.property) (hright := latticeFrequency.property)
  let U := gridScalarValue u
  let D := gridScalarValue d
  let A := gridScalarValue latticeFrequency
  change U=0 at hu
  change D=A*(1+U*U) at hd
  change D=A
  rw [hu] at hd
  grind only

end
end ComputableAnalysis.ModularForms
