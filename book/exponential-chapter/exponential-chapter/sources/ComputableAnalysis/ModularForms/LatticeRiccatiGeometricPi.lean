import ComputableAnalysis.ModularForms.LatticeDerivativeNomeQuotient
import ComputableAnalysis.ModularForms.NomeRiccatiConstant

/-! The actual lattice Riccati constant has the geometric nome normalization. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem latticeFrequency_geometricPiScalar : latticeFrequency.val.Equiv geometricPiScalar.val := by
  have he := ofRealRaw_equiv_of_equiv (realPart_valid latticeFrequency.property)
    (RealRaw.scaleRat_valid GeometricPiRotation.halfPi_valid) latticeFrequency_geometric_pi
  have hc : (ofRealRaw (RealRaw.scaleRat 2 GeometricPiRotation.halfPi)).Equiv
      geometricPiScalar.val := by
    intro n
    apply (compareAt_overlap_iff _ _ n n).2
    have ho := valid_ordered geometricPiScalar.property n
    simpa only [geometricPiScalar,ofRealRaw,RealRaw.scaleRat,RealRaw.scaleRatCompute,
      scaleRat,QBox.scaleRat,if_pos (show (0:Rat)≤2 by decide +kernel),Rat.mul_zero]
      using (show (geometricPiScalar.val.compute n).Overlaps (geometricPiScalar.val.compute n)
        from ⟨ho,ho⟩)
  exact equiv_trans latticeFrequency.property
    (ofRealRaw_valid _ (realPart_valid latticeFrequency.property)) geometricPiScalar.property
    latticeFrequency_real_embedding
    (equiv_trans (ofRealRaw_valid _ (realPart_valid latticeFrequency.property))
      (ofRealRaw_valid _ (RealRaw.scaleRat_valid GeometricPiRotation.halfPi_valid))
      geometricPiScalar.property he hc)

theorem latticeRiccatiConstant_geometric_pi_square :
    pairedRiccatiCenterConstant.val.Equiv
      (neg (mul geometricPiScalar.val geometricPiScalar.val)) := by
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid latticeFrequency.property latticeFrequency.property)
    (hright := neg_valid pairedRiccatiCenterConstant.property) latticeFrequency_complex_square_identity
  have hf := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := latticeFrequency.property)
    (hright := geometricPiScalar.property) latticeFrequency_geometricPiScalar
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := pairedRiccatiCenterConstant.property)
    (hright := neg_valid (mul_valid geometricPiScalar.property geometricPiScalar.property))
  let A := gridScalarValue latticeFrequency
  let P := gridScalarValue geometricPiScalar
  let C := gridScalarValue pairedRiccatiCenterConstant
  change A*A= -C at hs
  change A=P at hf
  change C= -(P*P)
  rw [hf] at hs
  grind only

theorem latticeRiccatiConstant_nomeConstant : pairedRiccatiCenterConstant.val.Equiv
    (scaleRat (1/4) (mul nomeSlope.val nomeSlope.val)) :=
  equiv_trans pairedRiccatiCenterConstant.property
    (neg_valid (mul_valid geometricPiScalar.property geometricPiScalar.property))
    (scaleRat_valid (mul_valid nomeSlope.property nomeSlope.property))
    latticeRiccatiConstant_geometric_pi_square (equiv_symm nomeRiccatiConstant_pi_square)

end ComputableAnalysis.ModularForms
