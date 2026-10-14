import ComputableAnalysis.ModularForms.NormalizedNomeCotangent
import ComputableAnalysis.ModularForms.ImaginaryUnitAlgebra

/-! The geometric pi square in the normalized nome differential equation. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def geometricPiScalar : Scalar :=
  ⟨scaleRat 2 (ofRealRaw GeometricPiRotation.halfPi),
    scaleRat_valid (ofRealRaw_valid _ GeometricPiRotation.halfPi_valid)⟩

theorem nomeRiccatiConstant_pi_square :
    (scaleRat (1/4) (mul nomeSlope.val nomeSlope.val)).Equiv
      (neg (mul geometricPiScalar.val geometricPiScalar.val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := scaleRat_valid (mul_valid nomeSlope.property nomeSlope.property))
    (hright := neg_valid (mul_valid geometricPiScalar.property geometricPiScalar.property))
  let p : Scalar := ⟨ofRealRaw GeometricPiRotation.halfPi,
    ofRealRaw_valid _ GeometricPiRotation.halfPi_valid⟩
  let P := ComplexRawQuotient.ofRaw p.val p.property
  have hi := mulI_class p
  change ComplexRawQuotient.scaleRat (1/4)
    (ComplexRawQuotient.scaleRat 4 (ComplexRawQuotient.ofRaw (mulI p.val) (mulI_valid p.property)) *
      ComplexRawQuotient.scaleRat 4 (ComplexRawQuotient.ofRaw (mulI p.val) (mulI_valid p.property))) =
    -(ComplexRawQuotient.scaleRat 2 P * ComplexRawQuotient.scaleRat 2 P)
  rw [hi,ComplexRawQuotient.scaleRat_mul_scaleRat,ComplexRawQuotient.scaleRat_scaleRat,
    ComplexRawQuotient.scaleRat_mul_scaleRat,ComplexRawQuotient.neg_scaleRat]
  have ha : (imaginaryUnitValue*P)*(imaginaryUnitValue*P)=
      (imaginaryUnitValue*imaginaryUnitValue)*(P*P) := by grind only
  rw [ha,imaginaryUnitValue_square]
  have hm : (((-1:Int):ScalarAlgebra.Value)*(P*P)) = -(P*P) := by grind only
  rw [hm,ComplexRawQuotient.neg_eq_scaleRat_neg_one,ComplexRawQuotient.scaleRat_scaleRat]
  congr 1
  decide +kernel

theorem normalizedNomeCotangent_riccati_pi (z : Scalar) (hz : normalizedNomeCotangentMap.domain z) :
    (normalizedNomeCotangentDerivative z hz).val.Equiv
      (sub (neg (mul geometricPiScalar.val geometricPiScalar.val))
        (mul (normalizedNomeCotangentMap.eval z hz).val (normalizedNomeCotangentMap.eval z hz).val)) :=
  equiv_trans (normalizedNomeCotangentDerivative z hz).property
    (sub_valid (scaleRat_valid (mul_valid nomeSlope.property nomeSlope.property))
      (mul_valid (normalizedNomeCotangentMap.eval z hz).property (normalizedNomeCotangentMap.eval z hz).property))
    (sub_valid (neg_valid (mul_valid geometricPiScalar.property geometricPiScalar.property))
      (mul_valid (normalizedNomeCotangentMap.eval z hz).property (normalizedNomeCotangentMap.eval z hz).property))
    (normalizedNomeCotangent_riccati z hz)
    (FunctionTheory.sub_congr nomeRiccatiConstant_pi_square
      (equiv_refl _ (mul_valid (normalizedNomeCotangentMap.eval z hz).property (normalizedNomeCotangentMap.eval z hz).property)))

end ComputableAnalysis.ModularForms
