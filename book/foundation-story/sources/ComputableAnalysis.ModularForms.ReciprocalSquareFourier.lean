import ComputableAnalysis.ModularForms.PairedReciprocalSquareSum
import ComputableAnalysis.ModularForms.WeightedNomeQuotient

/-! Actual reciprocal-square Fourier expansion on a justified nome disk. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedReciprocalSquareSum_fourier (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Rat) (hr : 0≤r) (hlocal : 4*r≤(1:Rat)/2) (hq : Small (nome.eval z hz).val r) :
    (pairedReciprocalSquareSum z hz).val.Equiv
      (neg (scaleRat 4 (mul (mul latticeFrequency.val latticeFrequency.val)
        (weightedNomeSum (nome.eval z hz) r)))) := by
  let q := nome.eval z hz
  let j := RepresentedReciprocal.inverse (nomeDenominator q) (nome_upper_denominator_nonzero z hz)
  have hs := weightedNomeSum_quotient q r hr hlocal hq (nome_upper_denominator_nonzero z hz)
  have ha := mul_valid latticeFrequency.property latticeFrequency.property
  have vs := weightedNomeSum_valid q r hr hlocal hq
  have vj := mul_valid q.property (mul_valid j.property j.property)
  have hm := mul_equiv ha ha vj vs (equiv_refl _ ha) (equiv_symm hs)
  exact equiv_trans (pairedReciprocalSquareSum z hz).property
    (neg_valid (scaleRat_valid (r := 4) (mul_valid ha vj)))
    (neg_valid (scaleRat_valid (r := 4) (mul_valid ha vs)))
    (pairedReciprocalSquareSum_nome_quotient z hz)
    (neg_equiv (scaleRat_equiv (r := 4) hm))

end ComputableAnalysis.ModularForms
