import ComputableAnalysis.ModularForms.ImaginaryUnit
import ComputableAnalysis.ModularForms.LatticeFrequencyNormalization
import ComputableAnalysis.ModularForms.CotangentRationalKernel

/-! The Cayley transform of the actual lattice tangent satisfies a linear rotation equation. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
noncomputable section
set_option maxHeartbeats 1000000

theorem latticeImaginaryUnit_square :
    gridScalarValue latticeImaginaryUnit*gridScalarValue latticeImaginaryUnit= -1 := by
  have h := rationalPole_mul_values ⟨0,1⟩ ⟨0,1⟩
  have hc : QComplex.mul ⟨0,1⟩ ⟨0,1⟩=⟨-1,0⟩ := by decide +kernel
  rw [hc] at h
  have hi' := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := scaleRat_valid (r := -1) (ofQComplex_valid _)) (hright := ofQComplex_valid _)
    (rationalScalarOne_equiv (-1))
  change ComplexRawQuotient.scaleRat (-1) 1=
    gridScalarValue (rationalRectangleScalar ⟨-1,0⟩) at hi'
  have hn := ComplexRawQuotient.neg_eq_scaleRat_neg_one (1:ScalarAlgebra.Value)
  change gridScalarValue (rationalRectangleScalar ⟨-1,0⟩)=
    gridScalarValue latticeImaginaryUnit*gridScalarValue latticeImaginaryUnit at h
  exact h.symm.trans (hi'.symm.trans hn.symm)

def latticeImaginaryTangentMap : DomainFunctions.Map :=
  compose (affine ⟨zero,ofQComplex_valid _⟩ latticeImaginaryUnit) normalizedLatticeTangentMap

def latticeImaginaryTangentMap_holomorphic : Holomorphic latticeImaginaryTangentMap :=
  (affine_holomorphic ⟨zero,ofQComplex_valid _⟩ latticeImaginaryUnit).compose
    normalizedLatticeTangentMap_holomorphic

def latticeCayleyRotationMap : DomainFunctions.Map :=
  compose cotangentRationalMap latticeImaginaryTangentMap

def latticeCayleyRotationMap_holomorphic : Holomorphic latticeCayleyRotationMap :=
  cotangentRationalMap_holomorphic.compose latticeImaginaryTangentMap_holomorphic

def latticeRotationSlope : Scalar :=
  ⟨add (mul latticeImaginaryUnit.val latticeFrequency.val)
    (mul latticeImaginaryUnit.val latticeFrequency.val),
    add_valid (mul_valid latticeImaginaryUnit.property latticeFrequency.property)
      (mul_valid latticeImaginaryUnit.property latticeFrequency.property)⟩

theorem latticeCayleyRotation_differential_identity (z : Scalar)
    (hz : latticeCayleyRotationMap.domain z) :
    (latticeCayleyRotationMap_holomorphic.derivative z hz).val.Equiv
      (mul latticeRotationSlope.val (latticeCayleyRotationMap.eval z hz).val) := by
  let hq := compose_inner_mem hz
  let q := latticeImaginaryTangentMap.eval z hq
  let hc := compose_outer_mem hz
  let j := nomeRationalInverseMap.eval q hc
  let hu := compose_inner_mem hq
  let u := normalizedLatticeTangentMap.eval z hu
  let d := normalizedLatticeTangentMap_holomorphic.derivative z hu
  have hj := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator q).property j.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (nomeDenominator q) (compose_outer_mem hc))
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := d.property)
    (hright := mul_valid latticeFrequency.property
      (add_valid (ofQComplex_valid _) (mul_valid u.property u.property)))
    (normalizedLatticeTangent_differential_identity z hu)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeCayleyRotationMap_holomorphic.derivative z hz).property)
    (hright := mul_valid latticeRotationSlope.property (latticeCayleyRotationMap.eval z hz).property)
  let U := gridScalarValue u
  let D := gridScalarValue d
  let A := gridScalarValue latticeFrequency
  let I := gridScalarValue latticeImaginaryUnit
  let J := gridScalarValue j
  have hi : I*I= -1 := latticeImaginaryUnit_square
  change (1-(0+I*U))*J=1 at hj
  change D=A*(1+U*U) at hd
  change (((-(J*J)*(-1))*(1+1*(0+I*U))+J*1)*(I*D))=
    (I*A+I*A)*(J*(1+1*(0+I*U)))
  rw [hd]
  grind only

theorem latticeImaginaryTangent_center_mem (z : Scalar) (he : z.val.Equiv zero) :
    latticeImaginaryTangentMap.domain z := ⟨normalizedLatticeTangent_center_mem z he,trivial⟩

theorem latticeImaginaryTangent_center_zero (z : Scalar) (he : z.val.Equiv zero) :
    (latticeImaginaryTangentMap.eval z (latticeImaginaryTangent_center_mem z he)).val.Equiv zero := by
  have hu := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (normalizedLatticeTangentMap.eval z (normalizedLatticeTangent_center_mem z he)).property)
    (hright := ofQComplex_valid _) (normalizedLatticeTangent_center_zero z he)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeImaginaryTangentMap.eval z (latticeImaginaryTangent_center_mem z he)).property)
    (hright := ofQComplex_valid _)
  let U := gridScalarValue (normalizedLatticeTangentMap.eval z (normalizedLatticeTangent_center_mem z he))
  let I := gridScalarValue latticeImaginaryUnit
  change U=0 at hu
  change 0+I*U=0
  rw [hu]
  grind only

theorem latticeCayleyRotation_center_mem (z : Scalar) (he : z.val.Equiv zero) :
    latticeCayleyRotationMap.domain z := by
  let hq := latticeImaginaryTangent_center_mem z he
  let q := latticeImaginaryTangentMap.eval z hq
  have hzero := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := q.property) (hright := ofQComplex_valid _)
    (latticeImaginaryTangent_center_zero z he)
  have hp : (mul (nomeDenominator q).val (ofQComplex QComplex.one)).Equiv (ofQComplex QComplex.one) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid (nomeDenominator q).property (ofQComplex_valid _)) (hright := ofQComplex_valid _)
    let Q := gridScalarValue q
    change Q=0 at hzero
    change (1-Q)*1=1
    rw [hzero]
    grind only
  exact ⟨hq,(cotangentRationalMap_domain q).mpr
    (RepresentedReciprocal.nonzero_of_inverse (nomeDenominator q)
      ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩ hp)⟩

theorem latticeCayleyRotation_center_one (z : Scalar) (he : z.val.Equiv zero) :
    (latticeCayleyRotationMap.eval z (latticeCayleyRotation_center_mem z he)).val.Equiv
      (ofQComplex QComplex.one) := by
  let hz := latticeCayleyRotation_center_mem z he
  let q := latticeImaginaryTangentMap.eval z (compose_inner_mem hz)
  let hc := compose_outer_mem hz
  let j := nomeRationalInverseMap.eval q hc
  have hq := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := q.property) (hright := ofQComplex_valid _)
    (latticeImaginaryTangent_center_zero z he)
  have hj := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator q).property j.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (nomeDenominator q) (compose_outer_mem hc))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeCayleyRotationMap.eval z hz).property) (hright := ofQComplex_valid _)
  let Q := gridScalarValue q
  let J := gridScalarValue j
  change Q=0 at hq
  change (1-Q)*J=1 at hj
  change J*(1+1*Q)=1
  rw [hq] at hj ⊢
  grind only

end
end ComputableAnalysis.ModularForms
