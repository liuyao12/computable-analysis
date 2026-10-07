import ComputableAnalysis.ModularForms.LatticeGeometricHalfAngle

/-! The actual lattice rotation agrees with the geometric nome. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem latticeRotationSlope_nomeSlope : latticeRotationSlope.val.Equiv nomeSlope.val := by
  have hh := imaginaryAxis_equiv latticeHalfFrequencyRotationInput.valid
    GeometricPiRotation.halfPi_valid latticeHalfFrequency_geometric_halfPi
  have hs := scaleRat_equiv (r := 4) hh
  exact equiv_trans latticeRotationSlope.property
    (scaleRat_valid latticeHalfFrequencyImaginary.property) nomeSlope.property
    (equiv_symm latticeHalfFrequency_fourfold_exponent) hs

theorem latticeRotationExponential_nome (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (latticeRotationExponentialMap.eval z (latticeRotationExponential_mem z)).val.Equiv
      (nome.eval z hz).val := by
  let a := (DomainFunctions.affine ⟨zero,ofQComplex_valid _⟩ latticeRotationSlope).eval z trivial
  let b := nomeExponentMap.eval z hz
  have ha : a.val.Equiv (mul latticeRotationSlope.val z.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := a.property)
      (hright := mul_valid latticeRotationSlope.property z.property)
    change 0+gridScalarValue latticeRotationSlope*gridScalarValue z=
      gridScalarValue latticeRotationSlope*gridScalarValue z
    grind only
  have hm := mul_equiv latticeRotationSlope.property nomeSlope.property z.property z.property
    latticeRotationSlope_nomeSlope (equiv_refl _ z.property)
  have hab := equiv_trans a.property (mul_valid latticeRotationSlope.property z.property)
    b.property ha hm
  exact entireExponentialValue_congr a b hab

theorem latticeCayleyRotation_nome (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (latticeCayleyRotationMap.eval z (latticeCayleyRotation_upper_mem z hz)).val.Equiv
      (nome.eval z hz).val := by
  exact equiv_trans (latticeCayleyRotationMap.eval z (latticeCayleyRotation_upper_mem z hz)).property
    (latticeRotationExponentialMap.eval z (latticeRotationExponential_mem z)).property
    (nome.eval z hz).property (latticeCayleyRotation_upper_exponential_agreement z hz)
    (latticeRotationExponential_nome z hz)

end ComputableAnalysis.ModularForms
