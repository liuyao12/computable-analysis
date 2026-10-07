import ComputableAnalysis.ModularForms.PairedDivisionQuadraticCoefficientIdentity
import ComputableAnalysis.ModularForms.LatticeRiccatiGeometricPi

/-! Exact geometric-pi evaluation of the actual center coefficients. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- The actual inverse-square center coefficient has its geometric-pi value. -/
theorem pairedCenterConstantSum_pi_square :
    pairedCenterConstantSum.Equiv (scaleRat (-1/3) (mul geometricPiScalar.val geometricPiScalar.val)) := by
  have he := equiv_trans (add_valid pairedCenterConstantSum_valid
    (add_valid pairedCenterConstantSum_valid pairedCenterConstantSum_valid))
    pairedRiccatiCenterConstant.property (neg_valid (mul_valid geometricPiScalar.property geometricPiScalar.property))
    (equiv_symm pairedRiccatiCenterConstant_center_coefficient) latticeRiccatiConstant_geometric_pi_square
  have h := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := add_valid pairedCenterConstantSum_valid (add_valid pairedCenterConstantSum_valid pairedCenterConstantSum_valid))
    (hright := neg_valid (mul_valid geometricPiScalar.property geometricPiScalar.property)) he
  let A := ComplexRawQuotient.ofRaw pairedCenterConstantSum pairedCenterConstantSum_valid
  let P := ComplexRawQuotient.ofRaw geometricPiScalar.val geometricPiScalar.property
  change A+(A+A)= -(P*P) at h
  have h3 : ComplexRawQuotient.scaleRat 3 A=A+(A+A) := by
    have hn := ScalarAlgebra.scale_natural 3 A
    rw [show ((3:Nat):Rat)=3 by decide +kernel] at hn
    rw [hn]
    grind only
  rw [←h3] at h
  have hs := congrArg (ComplexRawQuotient.scaleRat (1/3)) h
  rw [ComplexRawQuotient.scaleRat_scaleRat,show (1/3:Rat)*3=1 by decide +kernel,
    ComplexRawQuotient.scaleRat_one,ComplexRawQuotient.neg_eq_scaleRat_neg_one,
    ComplexRawQuotient.scaleRat_scaleRat,show (1/3:Rat)*(-1)= -1/3 by decide +kernel] at hs
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := pairedCenterConstantSum_valid)
    (hright := scaleRat_valid (mul_valid geometricPiScalar.property geometricPiScalar.property))
  exact hs

/-- Exact inverse-fourth quadratic coefficient, using the represented geometric pi. -/
theorem pairedCenterQuadraticSum_pi_fourth :
    pairedCenterQuadraticSum.Equiv (scaleRat (-1/45) (LocalODE.power geometricPiScalar.val 4)) := by
  have ha := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := pairedCenterConstantSum_valid)
    (hright := scaleRat_valid (mul_valid geometricPiScalar.property geometricPiScalar.property))
    pairedCenterConstantSum_pi_square
  have hb := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := pairedCenterQuadraticSum_valid)
    (hright := scaleRat_valid (mul_valid pairedCenterConstantSum_valid pairedCenterConstantSum_valid))
    pairedCenterQuadraticSum_center_square
  let A := ComplexRawQuotient.ofRaw pairedCenterConstantSum pairedCenterConstantSum_valid
  let B := ComplexRawQuotient.ofRaw pairedCenterQuadraticSum pairedCenterQuadraticSum_valid
  let P := ComplexRawQuotient.ofRaw geometricPiScalar.val geometricPiScalar.property
  change A=ComplexRawQuotient.scaleRat (-1/3) (P*P) at ha
  change B=ComplexRawQuotient.scaleRat (-1/5) (A*A) at hb
  rw [ha,ComplexRawQuotient.scaleRat_mul_scaleRat,ComplexRawQuotient.scaleRat_scaleRat] at hb
  have hr : (-1/5:Rat)*((-1/3)*(-1/3))= -1/45 := by decide +kernel
  rw [hr] at hb
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := pairedCenterQuadraticSum_valid)
    (hright := scaleRat_valid (LocalODE.power_valid _ geometricPiScalar.property 4))
  change B=ComplexRawQuotient.scaleRat (-1/45)
    (ComplexRawQuotient.ofRaw (LocalODE.power geometricPiScalar.val 4) (LocalODE.power_valid _ geometricPiScalar.property 4))
  rw [ScalarAlgebra.ofRaw_power _ geometricPiScalar.property]
  change B=ComplexRawQuotient.scaleRat (-1/45) (P^4)
  have hp : P^4=(P*P)*(P*P) := by grind only
  rw [hp]
  exact hb

/-- The actual inverse-fourth second-derivative center sum has its exact pi value. -/
theorem pairedZeroFourthSum_pi_fourth :
    pairedZeroFourthSum.Equiv (scaleRat (-2/45) (LocalODE.power geometricPiScalar.val 4)) := by
  have h1 := scaleRat_equiv (r := (2:Rat)) pairedCenterQuadraticSum_pi_fourth
  have h2 : (scaleRat 2 (scaleRat (-1/45) (LocalODE.power geometricPiScalar.val 4))).Equiv
      (scaleRat (-2/45) (LocalODE.power geometricPiScalar.val 4)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := scaleRat_valid (scaleRat_valid (LocalODE.power_valid _ geometricPiScalar.property 4)))
      (hright := scaleRat_valid (LocalODE.power_valid _ geometricPiScalar.property 4))
    change ComplexRawQuotient.scaleRat 2 (ComplexRawQuotient.scaleRat (-1/45)
      (ComplexRawQuotient.ofRaw (LocalODE.power geometricPiScalar.val 4) (LocalODE.power_valid _ geometricPiScalar.property 4)))=
      ComplexRawQuotient.scaleRat (-2/45)
        (ComplexRawQuotient.ofRaw (LocalODE.power geometricPiScalar.val 4) (LocalODE.power_valid _ geometricPiScalar.property 4))
    rw [ComplexRawQuotient.scaleRat_scaleRat,show (2:Rat)*(-1/45)= -2/45 by decide +kernel]
  exact equiv_trans pairedZeroFourthSum_valid (scaleRat_valid pairedCenterQuadraticSum_valid)
    (scaleRat_valid (LocalODE.power_valid _ geometricPiScalar.property 4)) pairedZeroFourthSum_quadratic_coefficient
    (equiv_trans (scaleRat_valid pairedCenterQuadraticSum_valid)
      (scaleRat_valid (scaleRat_valid (LocalODE.power_valid _ geometricPiScalar.property 4)))
      (scaleRat_valid (LocalODE.power_valid _ geometricPiScalar.property 4)) h1 h2)

end ComputableAnalysis.ModularForms
