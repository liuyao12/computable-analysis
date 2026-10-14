import ComputableAnalysis.ModularForms.UpperLatticeRotationExponential

/-! The actual Cayley quotient equals the constructed exponential throughout the upper half-plane. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
noncomputable section

theorem latticeImaginaryTangent_upper_mem (z : Scalar) (hz : InUpperHalfPlane z.val) :
    latticeImaginaryTangentMap.domain z :=
  ⟨⟨continuedLatticeReciprocal_upper_mem z hz,trivial⟩,trivial⟩

theorem latticeCayley_upper_denominator_agreement (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (nomeDenominator (latticeImaginaryTangentMap.eval z (latticeImaginaryTangent_upper_mem z hz))).val.Equiv
      (latticeRotationCrossDenominatorMap.eval z (latticeRotationCross_upper_mem z hz).1).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (nomeDenominator (latticeImaginaryTangentMap.eval z (latticeImaginaryTangent_upper_mem z hz))).property)
    (hright := (latticeRotationCrossDenominatorMap.eval z (latticeRotationCross_upper_mem z hz).1).property)
  let U := gridScalarValue (normalizedLatticeTangentMap.eval z
    (compose_inner_mem (latticeImaginaryTangent_upper_mem z hz)))
  let I := gridScalarValue latticeImaginaryUnit
  change 1-(0+I*U)=1+(-I)*U
  grind only

theorem latticeCayleyRotation_upper_mem (z : Scalar) (hz : InUpperHalfPlane z.val) :
    latticeCayleyRotationMap.domain z :=
  ⟨latticeImaginaryTangent_upper_mem z hz,
    (cotangentRationalMap_domain _).mpr
      ((NonzeroBoxSearch.nonzero_congr _ _ (latticeCayley_upper_denominator_agreement z hz)).mpr
        (latticeRotationCross_upper_denominator_nonzero z hz))⟩

theorem latticeCayleyRotation_upper_exponential_agreement (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (latticeCayleyRotationMap.eval z (latticeCayleyRotation_upper_mem z hz)).val.Equiv
      (latticeRotationExponentialMap.eval z (latticeRotationExponential_mem z)).val := by
  let hc := latticeCayleyRotation_upper_mem z hz
  let q := latticeImaginaryTangentMap.eval z (compose_inner_mem hc)
  let hq := compose_outer_mem hc
  let j := nomeRationalInverseMap.eval q hq
  let u := normalizedLatticeTangentMap.eval z (compose_inner_mem (compose_inner_mem hc))
  let e := latticeRotationExponentialMap.eval z (latticeRotationExponential_mem z)
  have hj := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator q).property j.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (nomeDenominator q) (compose_outer_mem hq))
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (latticeRotationCrossDenominatorMap.eval z (latticeRotationCross_upper_mem z hz).1).property e.property)
    (hright := (latticeRotationCrossNumeratorMap.eval z (latticeRotationCross_upper_mem z hz).2).property)
    (latticeRotationCross_upper_identity z hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeCayleyRotationMap.eval z hc).property) (hright := e.property)
  let U := gridScalarValue u
  let I := gridScalarValue latticeImaginaryUnit
  let J := gridScalarValue j
  let E := gridScalarValue e
  change (1-(0+I*U))*J=1 at hj
  change (1+(-I)*U)*E=1+I*U at he
  change J*(1+1*(0+I*U))=E
  grind only

theorem latticeImaginaryTangent_upper_period_int (z : Scalar) (hz : InUpperHalfPlane z.val) (k : Int) :
    (latticeImaginaryTangentMap.eval (integerShiftScalar z k)
      (latticeImaginaryTangent_upper_mem _ (integerShiftScalar_upper z hz k))).val.Equiv
      (latticeImaginaryTangentMap.eval z (latticeImaginaryTangent_upper_mem z hz)).val := by
  let w := integerShiftScalar z k
  let hw := integerShiftScalar_upper z hz k
  have hh := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (continuedLatticeReciprocalMap.eval w (continuedLatticeReciprocal_upper_mem w hw)).property)
    (hright := (continuedLatticeReciprocalMap.eval z (continuedLatticeReciprocal_upper_mem z hz)).property)
    (continuedLatticeReciprocal_upper_period_int z hz k)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeImaginaryTangentMap.eval w (latticeImaginaryTangent_upper_mem w hw)).property)
    (hright := (latticeImaginaryTangentMap.eval z (latticeImaginaryTangent_upper_mem z hz)).property)
  let W := gridScalarValue (continuedLatticeReciprocalMap.eval w (continuedLatticeReciprocal_upper_mem w hw))
  let Z := gridScalarValue (continuedLatticeReciprocalMap.eval z (continuedLatticeReciprocal_upper_mem z hz))
  let A := gridScalarValue latticeFrequency
  let I := gridScalarValue latticeImaginaryUnit
  change W=Z at hh
  change 0+I*(0+A*W)=0+I*(0+A*Z)
  rw [hh]

theorem latticeRotationExponential_upper_period_int (z : Scalar) (hz : InUpperHalfPlane z.val) (k : Int) :
    (latticeRotationExponentialMap.eval (integerShiftScalar z k)
      (latticeRotationExponential_mem _)).val.Equiv
      (latticeRotationExponentialMap.eval z (latticeRotationExponential_mem z)).val := by
  let w := integerShiftScalar z k
  let hw := integerShiftScalar_upper z hz k
  let hc := latticeCayleyRotation_upper_mem z hz
  let hd := latticeCayleyRotation_upper_mem w hw
  have hp := cotangentRationalMap.eval_congr
    (latticeImaginaryTangentMap.eval w (compose_inner_mem hd))
    (latticeImaginaryTangentMap.eval z (compose_inner_mem hc))
    (compose_outer_mem hd) (compose_outer_mem hc) (latticeImaginaryTangent_upper_period_int z hz k)
  exact equiv_trans (latticeRotationExponentialMap.eval w (latticeRotationExponential_mem w)).property
    (latticeCayleyRotationMap.eval w hd).property
    (latticeRotationExponentialMap.eval z (latticeRotationExponential_mem z)).property
    (equiv_symm (latticeCayleyRotation_upper_exponential_agreement w hw))
    (equiv_trans (latticeCayleyRotationMap.eval w hd).property
      (latticeCayleyRotationMap.eval z hc).property
      (latticeRotationExponentialMap.eval z (latticeRotationExponential_mem z)).property hp
      (latticeCayleyRotation_upper_exponential_agreement z hz))

end
end ComputableAnalysis.ModularForms
