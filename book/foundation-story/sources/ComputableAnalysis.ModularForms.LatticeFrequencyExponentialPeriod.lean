import ComputableAnalysis.ModularForms.UpperLatticeCayleyAgreement
import ComputableAnalysis.ModularForms.ExponentialInverse

/-! The constructed lattice frequency has exact exponential period. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
noncomputable section

theorem latticeRotationExponent_shift_one (z : Scalar) :
    ((affine ⟨zero,ofQComplex_valid _⟩ latticeRotationSlope).eval (integerShiftScalar z 1) trivial).val.Equiv
      (add ((affine ⟨zero,ofQComplex_valid _⟩ latticeRotationSlope).eval z trivial).val latticeRotationSlope.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((affine ⟨zero,ofQComplex_valid _⟩ latticeRotationSlope).eval (integerShiftScalar z 1) trivial).property)
    (hright := add_valid ((affine ⟨zero,ofQComplex_valid _⟩ latticeRotationSlope).eval z trivial).property latticeRotationSlope.property)
  let L := gridScalarValue latticeRotationSlope
  let Z := gridScalarValue z
  change 0+L*ComplexRawQuotient.ofRaw (integerAffine 1 1 z.val)
    (integerAffine_valid _ _ z.property)=(0+L*Z)+L
  rw [integerAffine_class]
  have h1 : ((1:Int):ScalarAlgebra.Value)=(1:ScalarAlgebra.Value) := by
    change ComplexRawQuotient.scaleRat 1 1=1
    exact ComplexRawQuotient.scaleRat_one _
  rw [h1]
  change 0+L*(1*Z+1)=(0+L*Z)+L
  grind only

theorem latticeFrequency_exponential_period :
    (entireExponentialValue latticeRotationSlope).val.Equiv (ofQComplex QComplex.one) := by
  let z := upperLatticeRotationAnchor
  let a := (affine ⟨zero,ofQComplex_valid _⟩ latticeRotationSlope).eval z trivial
  let b := (affine ⟨zero,ofQComplex_valid _⟩ latticeRotationSlope).eval (integerShiftScalar z 1) trivial
  let c : Scalar := ⟨add a.val latticeRotationSlope.val,add_valid a.property latticeRotationSlope.property⟩
  let d : Scalar := ⟨neg a.val,neg_valid a.property⟩
  have hadd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (entireExponentialValue a).property (entireExponentialValue latticeRotationSlope).property)
    (hright := (entireExponentialValue c).property) (entireExponential_addition a latticeRotationSlope)
  have hcongr := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (entireExponentialValue b).property) (hright := (entireExponentialValue c).property)
    (entireExponentialValue_congr b c (latticeRotationExponent_shift_one z))
  have hperiod := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (entireExponentialValue b).property) (hright := (entireExponentialValue a).property)
    (latticeRotationExponential_upper_period_int z upperLatticeRotationAnchor_upper 1)
  have hinv := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (entireExponentialValue a).property (entireExponentialValue d).property)
    (hright := ofQComplex_valid _) (entireExponential_inverse a)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (entireExponentialValue latticeRotationSlope).property) (hright := ofQComplex_valid _)
  let A := gridScalarValue (entireExponentialValue a)
  let B := gridScalarValue (entireExponentialValue b)
  let C := gridScalarValue (entireExponentialValue c)
  let D := gridScalarValue (entireExponentialValue d)
  let E := gridScalarValue (entireExponentialValue latticeRotationSlope)
  change A*E=C at hadd
  change B=C at hcongr
  change B=A at hperiod
  change A*D=1 at hinv
  change E=1
  grind only

end
end ComputableAnalysis.ModularForms
