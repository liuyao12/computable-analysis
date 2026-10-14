import ComputableAnalysis.ModularForms.CotangentNomeKernel
import ComputableAnalysis.RiemannHilbert.RepresentedReciprocal

/-! Nonzero nome denominators and agreement with general executable division. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def nomeDenominator (z : Scalar) : Scalar :=
  ⟨sub (ofQComplex QComplex.one) z.val,sub_valid (ofQComplex_valid _) z.property⟩

theorem nomeDenominator_nonzero (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 2*r≤(1:Rat)/2) (hz : Small z.val r) : NonzeroBoxSearch.Nonzero (nomeDenominator z) :=
  RepresentedReciprocal.nonzero_of_inverse (nomeDenominator z)
    ⟨nomeGeometricSum z r,nomeGeometricSum_valid z r hr hlocal hz⟩
    (nomeGeometricSum_inverse z r hr hlocal hz)

theorem nomeGeometricSum_reciprocal (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 2*r≤(1:Rat)/2) (hz : Small z.val r) :
    (nomeGeometricSum z r).Equiv
      (RepresentedReciprocal.inverse (nomeDenominator z)
        (nomeDenominator_nonzero z r hr hlocal hz)).val :=
  equiv_symm (RepresentedReciprocal.inverse_unique (nomeDenominator z)
    (nomeDenominator_nonzero z r hr hlocal hz)
    ⟨nomeGeometricSum z r,nomeGeometricSum_valid z r hr hlocal hz⟩
    (nomeGeometricSum_inverse z r hr hlocal hz))

theorem cotangentNomeKernel_quotient (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 2*r≤(1:Rat)/2) (hz : Small z.val r) :
    (cotangentNomeKernel z r).Equiv
      (mul (add (ofQComplex QComplex.one) z.val)
        (RepresentedReciprocal.inverse (nomeDenominator z)
          (nomeDenominator_nonzero z r hr hlocal hz)).val) := by
  let I := RepresentedReciprocal.inverse (nomeDenominator z) (nomeDenominator_nonzero z r hr hlocal hz)
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator z).property I.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (nomeDenominator z) (nomeDenominator_nonzero z r hr hlocal hz))
  have hk := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator z).property (cotangentNomeKernel_valid z r hr hlocal hz))
    (hright := add_valid (ofQComplex_valid _) z.property) (cotangentNomeKernel_identity z r hr hlocal hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := cotangentNomeKernel_valid z r hr hlocal hz)
    (hright := mul_valid (add_valid (ofQComplex_valid _) z.property) I.property)
  let D := ComplexRawQuotient.ofRaw (nomeDenominator z).val (nomeDenominator z).property
  let K := ComplexRawQuotient.ofRaw (cotangentNomeKernel z r) (cotangentNomeKernel_valid z r hr hlocal hz)
  let R := ComplexRawQuotient.ofRaw I.val I.property
  let N := ComplexRawQuotient.ofRaw (add (ofQComplex QComplex.one) z.val) (add_valid (ofQComplex_valid _) z.property)
  change D*R=1 at hi
  change D*K=N at hk
  change K=N*R
  grind only

end ComputableAnalysis.ModularForms
