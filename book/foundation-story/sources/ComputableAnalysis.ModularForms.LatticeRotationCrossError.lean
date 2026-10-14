import ComputableAnalysis.ModularForms.LatticeRotationExponential

/-! A denominator-free actual lattice/exponential comparison equation. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
noncomputable section
set_option maxHeartbeats 2000000

def latticeRotationCrossDenominatorMap : DomainFunctions.Map :=
  compose (affine ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩
    ⟨neg latticeImaginaryUnit.val,neg_valid latticeImaginaryUnit.property⟩) normalizedLatticeTangentMap

def latticeRotationCrossDenominatorMap_holomorphic : Holomorphic latticeRotationCrossDenominatorMap :=
  (affine_holomorphic ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩
    ⟨neg latticeImaginaryUnit.val,neg_valid latticeImaginaryUnit.property⟩).compose
      normalizedLatticeTangentMap_holomorphic

def latticeRotationCrossNumeratorMap : DomainFunctions.Map :=
  compose (affine ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩ latticeImaginaryUnit) normalizedLatticeTangentMap

def latticeRotationCrossNumeratorMap_holomorphic : Holomorphic latticeRotationCrossNumeratorMap :=
  (affine_holomorphic ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩ latticeImaginaryUnit).compose
    normalizedLatticeTangentMap_holomorphic

def latticeRotationCrossProductMap : DomainFunctions.Map :=
  productOn latticeRotationCrossDenominatorMap latticeRotationExponentialMap
    (fun z _ => latticeRotationExponential_mem z)

def latticeRotationCrossProductMap_holomorphic : Holomorphic latticeRotationCrossProductMap :=
  latticeRotationCrossDenominatorMap_holomorphic.productOn latticeRotationExponentialMap_holomorphic
    (fun z _ => latticeRotationExponential_mem z)

def latticeRotationCrossErrorMap : DomainFunctions.Map :=
  intersectionSum latticeRotationCrossProductMap (negate latticeRotationCrossNumeratorMap)

def latticeRotationCrossErrorMap_holomorphic : Holomorphic latticeRotationCrossErrorMap :=
  latticeRotationCrossProductMap_holomorphic.intersectionSum latticeRotationCrossNumeratorMap_holomorphic.negate

def latticeRotationCrossCoefficientMap : DomainFunctions.Map :=
  compose (affine (scalarProduct latticeImaginaryUnit latticeFrequency) latticeFrequency) normalizedLatticeTangentMap

def latticeRotationCrossCoefficientMap_holomorphic : Holomorphic latticeRotationCrossCoefficientMap :=
  (DomainFunctions.affine_holomorphic (scalarProduct latticeImaginaryUnit latticeFrequency) latticeFrequency).compose
    normalizedLatticeTangentMap_holomorphic

theorem latticeRotationCrossCoefficient_mem (z : Scalar) (hz : latticeRotationCrossErrorMap.domain z) :
    latticeRotationCrossCoefficientMap.domain z := ⟨compose_inner_mem hz.1,trivial⟩

theorem latticeRotationCrossError_equation (z : Scalar) (hz : latticeRotationCrossErrorMap.domain z) :
    (latticeRotationCrossErrorMap_holomorphic.derivative z hz).val.Equiv
      (mul (latticeRotationCrossCoefficientMap.eval z (latticeRotationCrossCoefficient_mem z hz)).val
        (latticeRotationCrossErrorMap.eval z hz).val) := by
  let hu := compose_inner_mem hz.1
  let u := normalizedLatticeTangentMap.eval z hu
  let d := normalizedLatticeTangentMap_holomorphic.derivative z hu
  let e := latticeRotationExponentialMap.eval z (latticeRotationExponential_mem z)
  let de := latticeRotationExponentialMap_holomorphic.derivative z (latticeRotationExponential_mem z)
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := d.property)
    (hright := mul_valid latticeFrequency.property (add_valid (ofQComplex_valid _) (mul_valid u.property u.property)))
    (normalizedLatticeTangent_differential_identity z hu)
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := de.property)
    (hright := mul_valid latticeRotationSlope.property e.property)
    (latticeRotationExponential_differential_identity z (latticeRotationExponential_mem z))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeRotationCrossErrorMap_holomorphic.derivative z hz).property)
    (hright := mul_valid (latticeRotationCrossCoefficientMap.eval z (latticeRotationCrossCoefficient_mem z hz)).property
      (latticeRotationCrossErrorMap.eval z hz).property)
  let U := gridScalarValue u
  let D := gridScalarValue d
  let E := gridScalarValue e
  let DE := gridScalarValue de
  let A := gridScalarValue latticeFrequency
  let I := gridScalarValue latticeImaginaryUnit
  have hi : I*I= -1 := latticeImaginaryUnit_square
  change D=A*(1+U*U) at hd
  change DE=(I*A+I*A)*E at he
  change ((-I)*D)*E+(1+(-I)*U)*DE+ -(I*D)=
    (I*A+A*U)*((1+(-I)*U)*E+ -(1+I*U))
  rw [hd,he]
  grind only

theorem latticeRotationCrossError_center_mem : latticeRotationCrossErrorMap.domain pairedZeroScalar :=
  ⟨⟨normalizedLatticeTangent_center_mem pairedZeroScalar (equiv_refl _ pairedZeroScalar.property),trivial⟩,
    ⟨normalizedLatticeTangent_center_mem pairedZeroScalar (equiv_refl _ pairedZeroScalar.property),trivial⟩⟩

theorem latticeRotationCrossError_center_zero :
    (latticeRotationCrossErrorMap.eval pairedZeroScalar latticeRotationCrossError_center_mem).val.Equiv zero := by
  let u := normalizedLatticeTangentMap.eval pairedZeroScalar (compose_inner_mem latticeRotationCrossError_center_mem.1)
  let e := latticeRotationExponentialMap.eval pairedZeroScalar (latticeRotationExponential_mem pairedZeroScalar)
  have hu := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := u.property) (hright := ofQComplex_valid _)
    (normalizedLatticeTangent_center_zero pairedZeroScalar (equiv_refl _ pairedZeroScalar.property))
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := e.property) (hright := ofQComplex_valid _)
    latticeRotationExponential_center_one
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeRotationCrossErrorMap.eval pairedZeroScalar latticeRotationCrossError_center_mem).property)
    (hright := ofQComplex_valid _)
  let U := gridScalarValue u
  let E := gridScalarValue e
  let I := gridScalarValue latticeImaginaryUnit
  change U=0 at hu
  change E=1 at he
  change (1+(-I)*U)*E+ -(1+I*U)=0
  rw [hu,he]
  grind only

def latticeRotationCrossRadius : QPos :=
  HomogeneousZeroNeighborhood.radius latticeRotationCrossErrorMap latticeRotationCrossCoefficientMap
    latticeRotationCrossErrorMap_holomorphic latticeRotationCrossCoefficientMap_holomorphic
    latticeRotationCrossCoefficient_mem pairedZeroScalar latticeRotationCrossError_center_mem

theorem latticeRotationCross_local_mem (z : Scalar)
    (hz : Small (sub z.val pairedZeroScalar.val) latticeRotationCrossRadius.val) :
    latticeRotationCrossErrorMap.domain z :=
  HomogeneousZeroNeighborhood.mem latticeRotationCrossErrorMap latticeRotationCrossCoefficientMap
    latticeRotationCrossErrorMap_holomorphic latticeRotationCrossCoefficientMap_holomorphic
    latticeRotationCrossCoefficient_mem pairedZeroScalar latticeRotationCrossError_center_mem z hz

theorem latticeRotationCross_local_zero (z : Scalar)
    (hz : Small (sub z.val pairedZeroScalar.val) latticeRotationCrossRadius.val) :
    (latticeRotationCrossErrorMap.eval z (latticeRotationCross_local_mem z hz)).val.Equiv zero :=
  HomogeneousZeroNeighborhood.zero_neighborhood latticeRotationCrossErrorMap latticeRotationCrossCoefficientMap
    latticeRotationCrossErrorMap_holomorphic latticeRotationCrossCoefficientMap_holomorphic
    latticeRotationCrossCoefficient_mem pairedZeroScalar latticeRotationCrossError_center_mem
    latticeRotationCrossError_equation latticeRotationCrossError_center_zero z hz

theorem latticeRotationCross_upper_mem (z : Scalar) (hz : InUpperHalfPlane z.val) :
    latticeRotationCrossErrorMap.domain z :=
  ⟨⟨⟨continuedLatticeReciprocal_upper_mem z hz,trivial⟩,trivial⟩,
    ⟨⟨continuedLatticeReciprocal_upper_mem z hz,trivial⟩,trivial⟩⟩

theorem latticeRotationCross_local_identity (z : Scalar)
    (hz : Small (sub z.val pairedZeroScalar.val) latticeRotationCrossRadius.val) :
    (mul (latticeRotationCrossDenominatorMap.eval z (latticeRotationCross_local_mem z hz).1).val
      (latticeRotationExponentialMap.eval z (latticeRotationExponential_mem z)).val).Equiv
      (latticeRotationCrossNumeratorMap.eval z (latticeRotationCross_local_mem z hz).2).val := by
  have hh := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (latticeRotationCrossErrorMap.eval z (latticeRotationCross_local_mem z hz)).property)
    (hright := ofQComplex_valid _) (latticeRotationCross_local_zero z hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (latticeRotationCrossDenominatorMap.eval z (latticeRotationCross_local_mem z hz).1).property
      (latticeRotationExponentialMap.eval z (latticeRotationExponential_mem z)).property)
    (hright := (latticeRotationCrossNumeratorMap.eval z (latticeRotationCross_local_mem z hz).2).property)
  let D := gridScalarValue (latticeRotationCrossDenominatorMap.eval z (latticeRotationCross_local_mem z hz).1)
  let E := gridScalarValue (latticeRotationExponentialMap.eval z (latticeRotationExponential_mem z))
  let N := gridScalarValue (latticeRotationCrossNumeratorMap.eval z (latticeRotationCross_local_mem z hz).2)
  change D*E+ -N=0 at hh
  change D*E=N
  grind only

end
end ComputableAnalysis.ModularForms
