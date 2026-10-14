import ComputableAnalysis.ModularForms.LatticeNomeDerivative

/-! Explicit rational nome expression for the actual lattice derivative. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem latticeDerivative_nome_quotient (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z
      (pairedGlobalOffPole_upper_mem z hz)).val.Equiv
      (scaleRat 4 (mul (mul latticeFrequency.val latticeFrequency.val)
        (mul (nome.eval z hz).val
          (mul (RepresentedReciprocal.inverse (nomeDenominator (nome.eval z hz))
            (nome_upper_denominator_nonzero z hz)).val
            (RepresentedReciprocal.inverse (nomeDenominator (nome.eval z hz))
              (nome_upper_denominator_nonzero z hz)).val)))) := by
  let q := nome.eval z hz
  let j := RepresentedReciprocal.inverse (nomeDenominator q) (nome_upper_denominator_nonzero z hz)
  let d := pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z (pairedGlobalOffPole_upper_mem z hz)
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := d.property)
    (hright := mul_valid latticeFourierCoefficient.property (upperNomeCotangentDerivative z hz).property)
    (latticePartialFraction_nome_derivative z hz)
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := latticeRotationSlope.property)
    (hright := nomeSlope.property) latticeRotationSlope_nomeSlope
  let D := gridScalarValue d
  let Q := gridScalarValue q
  let J := gridScalarValue j
  let A := gridScalarValue latticeFrequency
  let I := gridScalarValue latticeImaginaryUnit
  let S := gridScalarValue nomeSlope
  change D=(-(I*A))*((J*J+J*J)*(Q*S)) at hd
  change I*A+I*A=S at hs
  have hi : I*I= -1 := latticeImaginaryUnit_square
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := d.property)
    (hright := scaleRat_valid (mul_valid (mul_valid latticeFrequency.property latticeFrequency.property)
      (mul_valid q.property (mul_valid j.property j.property))))
  change D=ComplexRawQuotient.scaleRat 4 ((A*A)*(Q*(J*J)))
  have h4 : (4:Rat)=1+1+1+1 := by decide +kernel
  rw [h4,←ComplexRawQuotient.add_scaleRat,←ComplexRawQuotient.add_scaleRat,
    ←ComplexRawQuotient.add_scaleRat,ComplexRawQuotient.scaleRat_one]
  rw [←hs] at hd
  grind only

end ComputableAnalysis.ModularForms
