import ComputableAnalysis.ModularForms.PairedDivisionQuarticCoefficientIdentity

/-! Exact inverse-sixth center coefficient normalized by represented geometric pi. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- The actual constructed quartic coefficient has its exact geometric-pi value. -/
theorem pairedCenterQuarticSum_pi_sixth :
    pairedCenterQuarticSum.Equiv (scaleRat (-2/945) (LocalODE.power geometricPiScalar.val 6)) := by
  have ha := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := pairedCenterConstantSum_valid)
    (hright := scaleRat_valid (mul_valid geometricPiScalar.property geometricPiScalar.property))
    pairedCenterConstantSum_pi_square
  have hb := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := pairedCenterQuadraticSum_valid)
    (hright := scaleRat_valid (LocalODE.power_valid _ geometricPiScalar.property 4))
    pairedCenterQuadraticSum_pi_fourth
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := pairedCenterQuarticSum_valid)
    (hright := scaleRat_valid (mul_valid pairedCenterConstantSum_valid pairedCenterQuadraticSum_valid))
    pairedCenterQuarticSum_center_product
  let A := ComplexRawQuotient.ofRaw pairedCenterConstantSum pairedCenterConstantSum_valid
  let B := ComplexRawQuotient.ofRaw pairedCenterQuadraticSum pairedCenterQuadraticSum_valid
  let D := ComplexRawQuotient.ofRaw pairedCenterQuarticSum pairedCenterQuarticSum_valid
  let P := ComplexRawQuotient.ofRaw geometricPiScalar.val geometricPiScalar.property
  change A=ComplexRawQuotient.scaleRat (-1/3) (P*P) at ha
  change B=ComplexRawQuotient.scaleRat (-1/45)
    (ComplexRawQuotient.ofRaw (LocalODE.power geometricPiScalar.val 4) (LocalODE.power_valid _ geometricPiScalar.property 4)) at hb
  rw [ScalarAlgebra.ofRaw_power _ geometricPiScalar.property] at hb
  change B=ComplexRawQuotient.scaleRat (-1/45) (P^4) at hb
  change D=ComplexRawQuotient.scaleRat (-2/7) (A*B) at hd
  rw [ha,hb,ComplexRawQuotient.scaleRat_mul_scaleRat,ComplexRawQuotient.scaleRat_scaleRat] at hd
  rw [show (-2/7:Rat)*((-1/3)*(-1/45))= -2/945 by decide +kernel] at hd
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := pairedCenterQuarticSum_valid)
    (hright := scaleRat_valid (LocalODE.power_valid _ geometricPiScalar.property 6))
  change D=ComplexRawQuotient.scaleRat (-2/945)
    (ComplexRawQuotient.ofRaw (LocalODE.power geometricPiScalar.val 6) (LocalODE.power_valid _ geometricPiScalar.property 6))
  rw [ScalarAlgebra.ofRaw_power _ geometricPiScalar.property]
  change D=ComplexRawQuotient.scaleRat (-2/945) (P^6)
  have hp : P^6=(P*P)*(P^4) := by grind only
  rw [hp]
  exact hd

end ComputableAnalysis.ModularForms
