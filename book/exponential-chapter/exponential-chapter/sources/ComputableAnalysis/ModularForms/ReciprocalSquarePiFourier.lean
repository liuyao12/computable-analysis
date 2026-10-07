import ComputableAnalysis.ModularForms.ReciprocalSquareFourier
import ComputableAnalysis.ModularForms.LatticeRiccatiGeometricPi

/-! Geometric pi normalization of the actual reciprocal-square Fourier identity. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedReciprocalSquareSum_pi_fourier (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Rat) (hr : 0≤r) (hlocal : 4*r≤(1:Rat)/2) (hq : Small (nome.eval z hz).val r) :
    (pairedReciprocalSquareSum z hz).val.Equiv
      (neg (scaleRat 4 (mul (mul geometricPiScalar.val geometricPiScalar.val)
        (weightedNomeSum (nome.eval z hz) r)))) := by
  have vs := weightedNomeSum_valid (nome.eval z hz) r hr hlocal hq
  have ha := mul_valid latticeFrequency.property latticeFrequency.property
  have hb := mul_valid geometricPiScalar.property geometricPiScalar.property
  have hab := mul_equiv latticeFrequency.property geometricPiScalar.property
    latticeFrequency.property geometricPiScalar.property
    latticeFrequency_geometricPiScalar latticeFrequency_geometricPiScalar
  have hm := mul_equiv ha hb vs vs hab (equiv_refl _ vs)
  exact equiv_trans (pairedReciprocalSquareSum z hz).property
    (neg_valid (scaleRat_valid (r := 4) (mul_valid ha vs)))
    (neg_valid (scaleRat_valid (r := 4) (mul_valid hb vs)))
    (pairedReciprocalSquareSum_fourier z hz r hr hlocal hq)
    (neg_equiv (scaleRat_equiv (r := 4) hm))

end ComputableAnalysis.ModularForms
