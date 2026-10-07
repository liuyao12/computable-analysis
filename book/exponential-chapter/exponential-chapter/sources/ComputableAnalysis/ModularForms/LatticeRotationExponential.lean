import ComputableAnalysis.ModularForms.LatticeCayleyRotation
import ComputableAnalysis.ModularForms.ExponentialDerivative
import ComputableAnalysis.ModularForms.HomogeneousZeroNeighborhood

/-! The actual exponential comparison equation for lattice Cayley rotation. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
noncomputable section

def latticeRotationExponentialMap : DomainFunctions.Map :=
  compose entireExponential (affine ⟨zero,ofQComplex_valid _⟩ latticeRotationSlope)

def latticeRotationExponentialMap_holomorphic : Holomorphic latticeRotationExponentialMap :=
  entireExponential_holomorphic.compose (affine_holomorphic ⟨zero,ofQComplex_valid _⟩ latticeRotationSlope)

theorem latticeRotationExponential_mem (z : Scalar) : latticeRotationExponentialMap.domain z := ⟨trivial,trivial⟩

theorem latticeRotationExponential_differential_identity (z : Scalar)
    (hz : latticeRotationExponentialMap.domain z) :
    (latticeRotationExponentialMap_holomorphic.derivative z hz).val.Equiv
      (mul latticeRotationSlope.val (latticeRotationExponentialMap.eval z hz).val) := by
  let a := (affine ⟨zero,ofQComplex_valid _⟩ latticeRotationSlope).eval z trivial
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (entireExponential_holomorphic.derivative a trivial).property)
    (hright := (entireExponentialValue a).property) (entireExponential_derivative_value a)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeRotationExponentialMap_holomorphic.derivative z hz).property)
    (hright := mul_valid latticeRotationSlope.property (latticeRotationExponentialMap.eval z hz).property)
  let D := gridScalarValue (entireExponential_holomorphic.derivative a trivial)
  let E := gridScalarValue (entireExponentialValue a)
  let L := gridScalarValue latticeRotationSlope
  change D=E at hd
  change D*L=L*E
  rw [hd]
  grind only

def latticeRotationDifferenceMap : DomainFunctions.Map :=
  intersectionSum latticeCayleyRotationMap (negate latticeRotationExponentialMap)

def latticeRotationDifferenceMap_holomorphic : Holomorphic latticeRotationDifferenceMap :=
  latticeCayleyRotationMap_holomorphic.intersectionSum latticeRotationExponentialMap_holomorphic.negate

def latticeRotationCoefficientMap : DomainFunctions.Map :=
  affine latticeRotationSlope ⟨zero,ofQComplex_valid _⟩

def latticeRotationCoefficientMap_holomorphic : Holomorphic latticeRotationCoefficientMap :=
  affine_holomorphic latticeRotationSlope ⟨zero,ofQComplex_valid _⟩

theorem latticeRotationDifference_equation (z : Scalar) (hz : latticeRotationDifferenceMap.domain z) :
    (latticeRotationDifferenceMap_holomorphic.derivative z hz).val.Equiv
      (mul (latticeRotationCoefficientMap.eval z trivial).val (latticeRotationDifferenceMap.eval z hz).val) := by
  let r := latticeCayleyRotationMap.eval z hz.1
  let e := latticeRotationExponentialMap.eval z hz.2
  let dr := latticeCayleyRotationMap_holomorphic.derivative z hz.1
  let de := latticeRotationExponentialMap_holomorphic.derivative z hz.2
  have hr := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := dr.property)
    (hright := mul_valid latticeRotationSlope.property r.property) (latticeCayleyRotation_differential_identity z hz.1)
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := de.property)
    (hright := mul_valid latticeRotationSlope.property e.property) (latticeRotationExponential_differential_identity z hz.2)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeRotationDifferenceMap_holomorphic.derivative z hz).property)
    (hright := mul_valid (latticeRotationCoefficientMap.eval z trivial).property (latticeRotationDifferenceMap.eval z hz).property)
  let R := gridScalarValue r
  let E := gridScalarValue e
  let DR := gridScalarValue dr
  let DE := gridScalarValue de
  let L := gridScalarValue latticeRotationSlope
  let Z := gridScalarValue z
  change DR=L*R at hr
  change DE=L*E at he
  change DR+ -DE=(L+0*Z)*(R+ -E)
  rw [hr,he]
  grind only

theorem latticeRotationExponential_center_one :
    (latticeRotationExponentialMap.eval pairedZeroScalar (latticeRotationExponential_mem pairedZeroScalar)).val.Equiv
      (ofQComplex QComplex.one) := by
  let a := (affine ⟨zero,ofQComplex_valid _⟩ latticeRotationSlope).eval pairedZeroScalar trivial
  have ha : a.val.Equiv zero := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := a.property) (hright := ofQComplex_valid _)
    let L := gridScalarValue latticeRotationSlope
    change 0+L*0=0
    grind only
  exact equiv_trans (entireExponentialValue a).property
    (entireExponentialValue ⟨zero,ofQComplex_valid _⟩).property (ofQComplex_valid _)
    (entireExponentialValue_congr a ⟨zero,ofQComplex_valid _⟩ ha) entireExponential_zero

theorem latticeRotationDifference_center_mem : latticeRotationDifferenceMap.domain pairedZeroScalar :=
  ⟨latticeCayleyRotation_center_mem pairedZeroScalar (equiv_refl _ pairedZeroScalar.property),
    latticeRotationExponential_mem pairedZeroScalar⟩

theorem latticeRotationDifference_center_zero :
    (latticeRotationDifferenceMap.eval pairedZeroScalar latticeRotationDifference_center_mem).val.Equiv zero := by
  have hr := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (latticeCayleyRotationMap.eval pairedZeroScalar latticeRotationDifference_center_mem.1).property)
    (hright := ofQComplex_valid _)
    (latticeCayleyRotation_center_one pairedZeroScalar (equiv_refl _ pairedZeroScalar.property))
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (latticeRotationExponentialMap.eval pairedZeroScalar latticeRotationDifference_center_mem.2).property)
    (hright := ofQComplex_valid _) latticeRotationExponential_center_one
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeRotationDifferenceMap.eval pairedZeroScalar latticeRotationDifference_center_mem).property)
    (hright := ofQComplex_valid _)
  let R := gridScalarValue (latticeCayleyRotationMap.eval pairedZeroScalar latticeRotationDifference_center_mem.1)
  let E := gridScalarValue (latticeRotationExponentialMap.eval pairedZeroScalar latticeRotationDifference_center_mem.2)
  change R=1 at hr
  change E=1 at he
  change R+ -E=0
  rw [hr,he]
  grind only

def latticeRotationAgreementRadius : QPos :=
  HomogeneousZeroNeighborhood.radius latticeRotationDifferenceMap latticeRotationCoefficientMap
    latticeRotationDifferenceMap_holomorphic latticeRotationCoefficientMap_holomorphic
    (fun _ _ => trivial) pairedZeroScalar latticeRotationDifference_center_mem

theorem latticeRotationAgreement_mem (z : Scalar)
    (hz : Small (sub z.val pairedZeroScalar.val) latticeRotationAgreementRadius.val) :
    latticeRotationDifferenceMap.domain z :=
  HomogeneousZeroNeighborhood.mem latticeRotationDifferenceMap latticeRotationCoefficientMap
    latticeRotationDifferenceMap_holomorphic latticeRotationCoefficientMap_holomorphic
    (fun _ _ => trivial) pairedZeroScalar latticeRotationDifference_center_mem z hz

theorem latticeRotation_local_exponential_agreement (z : Scalar)
    (hz : Small (sub z.val pairedZeroScalar.val) latticeRotationAgreementRadius.val) :
    (latticeCayleyRotationMap.eval z (latticeRotationAgreement_mem z hz).1).val.Equiv
      (latticeRotationExponentialMap.eval z (latticeRotationAgreement_mem z hz).2).val := by
  have hh := HomogeneousZeroNeighborhood.zero_neighborhood
    latticeRotationDifferenceMap latticeRotationCoefficientMap
    latticeRotationDifferenceMap_holomorphic latticeRotationCoefficientMap_holomorphic
    (fun _ _ => trivial) pairedZeroScalar latticeRotationDifference_center_mem
    latticeRotationDifference_equation latticeRotationDifference_center_zero z hz
  have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (latticeRotationDifferenceMap.eval z (latticeRotationAgreement_mem z hz)).property)
    (hright := ofQComplex_valid _) hh
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeCayleyRotationMap.eval z (latticeRotationAgreement_mem z hz).1).property)
    (hright := (latticeRotationExponentialMap.eval z (latticeRotationAgreement_mem z hz).2).property)
  let R := gridScalarValue (latticeCayleyRotationMap.eval z (latticeRotationAgreement_mem z hz).1)
  let E := gridScalarValue (latticeRotationExponentialMap.eval z (latticeRotationAgreement_mem z hz).2)
  change R+ -E=0 at hv
  change R=E
  grind only

end
end ComputableAnalysis.ModularForms
