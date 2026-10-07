import ComputableAnalysis.ModularForms.LatticeTangentNomeProduct

/-! The actual lattice partial-fraction value equals its rational nome formula. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem latticePartialFraction_nome_formula (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (pairedGlobalOffPoleAssemblyMap.eval z (pairedGlobalOffPole_upper_mem z hz)).val.Equiv
      (neg (mul latticeImaginaryUnit.val
        (mul latticeFrequency.val (upperNomeCotangentMap.eval z hz).val))) := by
  let p := pairedGlobalOffPoleAssemblyMap.eval z (pairedGlobalOffPole_upper_mem z hz)
  let w := continuedLatticeReciprocalMap.eval z (continuedLatticeReciprocal_upper_mem z hz)
  let k := upperNomeCotangentMap.eval z hz
  let hu := (show normalizedLatticeTangentMap.domain z from
    ⟨continuedLatticeReciprocal_upper_mem z hz,trivial⟩)
  let u := normalizedLatticeTangentMap.eval z hu
  let j := RepresentedReciprocal.inverse p (upperLatticeKernel_nonzero z hz)
  have hw := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := w.property) (hright := j.property)
    (equiv_symm (continuedLatticeReciprocal_represented_inverse z hz))
  have hj := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid p.property j.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse p (upperLatticeKernel_nonzero z hz))
  have ht := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid u.property k.property)
    (hright := latticeImaginaryUnit.property) (latticeTangent_nomeCotangent_product z hz)
  let P := gridScalarValue p
  let W := gridScalarValue w
  let J := gridScalarValue j
  let K := gridScalarValue k
  let A := gridScalarValue latticeFrequency
  let I := gridScalarValue latticeImaginaryUnit
  change W=J at hw
  change P*J=1 at hj
  change (0+A*W)*K=I at ht
  have hi : I*I= -1 := latticeImaginaryUnit_square
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := p.property)
    (hright := neg_valid (mul_valid latticeImaginaryUnit.property
      (mul_valid latticeFrequency.property k.property)))
  change P= -(I*(A*K))
  rw [←hw] at hj
  have hpk : A*K=I*P := by grind only
  rw [hpk]
  grind only

end ComputableAnalysis.ModularForms
