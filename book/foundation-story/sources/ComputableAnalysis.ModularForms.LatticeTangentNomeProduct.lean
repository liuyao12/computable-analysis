import ComputableAnalysis.ModularForms.LatticeNomeAgreement
import ComputableAnalysis.ModularForms.NomeUpperCotangent

/-! Exact inversion algebra between the actual lattice tangent and nome kernel. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem latticeTangent_nomeCotangent_product (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (mul (normalizedLatticeTangentMap.eval z
      ⟨continuedLatticeReciprocal_upper_mem z hz,trivial⟩).val
      (upperNomeCotangentMap.eval z hz).val).Equiv latticeImaginaryUnit.val := by
  let hu := (show normalizedLatticeTangentMap.domain z from
    ⟨continuedLatticeReciprocal_upper_mem z hz,trivial⟩)
  let u := normalizedLatticeTangentMap.eval z hu
  let e := latticeRotationExponentialMap.eval z (latticeRotationExponential_mem z)
  let q := nome.eval z hz
  let k := upperNomeCotangentMap.eval z hz
  let j := RepresentedReciprocal.inverse (nomeDenominator q) (nome_upper_denominator_nonzero z hz)
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := e.property) (hright := q.property)
    (latticeRotationExponential_nome z hz)
  have hc := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (latticeRotationCrossDenominatorMap.eval z
      (latticeRotationCross_upper_mem z hz).1).property e.property)
    (hright := (latticeRotationCrossNumeratorMap.eval z
      (latticeRotationCross_upper_mem z hz).2).property)
    (latticeRotationCross_upper_identity z hz)
  have hk := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator q).property k.property)
    (hright := add_valid (ofQComplex_valid _) q.property)
    (cotangentRationalMap_identity q ((cotangentRationalMap_domain q).mpr
      (nome_upper_denominator_nonzero z hz)))
  have hj := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator q).property j.property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse _ _)
  let U := gridScalarValue u
  let E := gridScalarValue e
  let Q := gridScalarValue q
  let K := gridScalarValue k
  let J := gridScalarValue j
  let I := gridScalarValue latticeImaginaryUnit
  change E=Q at he
  change (1+(-I)*U)*E=1+I*U at hc
  change (1-Q)*K=1+Q at hk
  change (1-Q)*J=1 at hj
  have hi : I*I= -1 := latticeImaginaryUnit_square
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid u.property k.property) (hright := latticeImaginaryUnit.property)
  change U*K=I
  rw [he] at hc
  have hprod : (1-Q)*(U*K-I)=0 := by grind only
  grind only

end ComputableAnalysis.ModularForms
