import ComputableAnalysis.ModularForms.GeometricQuarterTurn
import ComputableAnalysis.ModularForms.ExponentialPowers

/-! Exact half-period phase for the actual entire exponential. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def imaginaryPiScalar : Scalar :=
  ⟨scaleRat 2 GeometricPiRotation.imaginaryHalf,scaleRat_valid GeometricPiRotation.imaginaryHalf_valid⟩

private theorem imaginaryUnit_square :
    (LocalODE.power (ofQComplex RotationSeries.imaginaryUnit) 2).Equiv (ofQComplex ⟨-1,0⟩) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  change ((LocalODE.power (ofQComplex RotationSeries.imaginaryUnit) 2).compute 0).Overlaps
    ((ofQComplex ⟨-1,0⟩).compute 0)
  decide +kernel

theorem entireExponential_imaginaryPi :
    (entireExponentialValue imaginaryPiScalar).val.Equiv (ofQComplex ⟨-1,0⟩) := by
  let z : Scalar := ⟨GeometricPiRotation.imaginaryHalf,GeometricPiRotation.imaginaryHalf_valid⟩
  have hn := entireExponential_nat_multiple z 2
  have hc : ((2:Nat):Rat)=(2:Rat) := by decide +kernel
  rw [hc] at hn
  have hp := LocalODE.power_congr _ _ (entireExponentialValue z).property
    (ofQComplex_valid _) entireExponential_geometric_quarterTurn 2
  exact equiv_trans (entireExponentialValue imaginaryPiScalar).property
    (LocalODE.power_valid _ (entireExponentialValue z).property 2) (ofQComplex_valid _) hn
    (equiv_trans (LocalODE.power_valid _ (entireExponentialValue z).property 2)
      (LocalODE.power_valid _ (ofQComplex_valid _) 2) (ofQComplex_valid _) hp imaginaryUnit_square)

private theorem mul_negativeOne (z : ComplexRaw) (hz : z.Valid) :
    (mul z (ofQComplex ⟨-1,0⟩)).Equiv (neg z) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid hz (ofQComplex_valid _)) (hright := neg_valid hz)
  change ComplexRawQuotient.ofRaw z hz * ComplexRawQuotient.ofQComplex ⟨-1,0⟩ =
    -ComplexRawQuotient.ofRaw z hz
  have hc : ComplexRawQuotient.ofQComplex ⟨-1,0⟩ = -(1:ScalarAlgebra.Value) := rfl
  rw [hc]
  grind only

theorem entireExponential_add_imaginaryPi (z : Scalar) :
    (entireExponentialValue ⟨add z.val imaginaryPiScalar.val,
      add_valid z.property imaginaryPiScalar.property⟩).val.Equiv
      (neg (entireExponentialValue z).val) := by
  have hz := (entireExponentialValue z).property
  have hm := mul_equiv hz hz (entireExponentialValue imaginaryPiScalar).property
    (ofQComplex_valid _) (equiv_refl _ hz) entireExponential_imaginaryPi
  exact equiv_trans (entireExponentialValue _).property
    (mul_valid hz (entireExponentialValue imaginaryPiScalar).property) (neg_valid hz)
    (equiv_symm (entireExponential_addition z imaginaryPiScalar))
    (equiv_trans (mul_valid hz (entireExponentialValue imaginaryPiScalar).property)
      (mul_valid hz (ofQComplex_valid _)) (neg_valid hz) hm (mul_negativeOne _ hz))

end ComputableAnalysis.ModularForms
