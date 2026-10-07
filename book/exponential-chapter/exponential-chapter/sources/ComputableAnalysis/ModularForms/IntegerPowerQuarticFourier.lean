import ComputableAnalysis.ModularForms.IntegerPowerRowQuartic
import ComputableAnalysis.ModularForms.NomeMomentCubicQuotient
import ComputableAnalysis.ModularForms.LatticePartialFractionNome

/-! Exact Fourier identity of the actual quartic row and cubic nome moment. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem integerReciprocalPowerRowSum_quartic_fourier (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Rat) (hr : 0≤r) (hlocal : 16*r≤(1:Rat)/2) (hq : Small (nome.eval z hz).val r) :
    (integerReciprocalPowerRowSum z hz 4 (by omega)).val.Equiv
      (scaleRat (8/3) (mul (LocalODE.power latticeFrequency.val 4)
        (polynomialNomeMomentSum (nome.eval z hz) r 3))) := by
  let q := nome.eval z hz
  let j := RepresentedReciprocal.inverse (nomeDenominator q) (nome_upper_denominator_nonzero z hz)
  have hl : polynomialNomeMomentRatio r 3≤(1:Rat)/2 := by
    rw [polynomialNomeMomentRatio_three]; exact hlocal
  have vs := polynomialNomeMomentSum_valid q r 3 hr hl hq
  have hf := integerReciprocalPowerRowSum_quartic_riccati z hz
  have hs := polynomialNomeMomentSum_three_quotient q r hr hlocal hq (nome_upper_denominator_nonzero z hz)
  have hpi := equiv_trans (pairedPartialFractionMap.eval z hz).property
    (pairedGlobalOffPoleAssemblyMap.eval z (pairedGlobalOffPole_upper_mem z hz)).property
    (neg_valid (mul_valid latticeImaginaryUnit.property
      (mul_valid latticeFrequency.property (upperNomeCotangentMap.eval z hz).property)))
    (equiv_symm (pairedGlobalOffPoleAssemblyMap_upper_agreement z hz)) (latticePartialFraction_nome_formula z hz)
  have h2 := equiv_trans (integerReciprocalPowerRowSum z hz 2 (by omega)).property
    (pairedReciprocalSquareSum z hz).property
    (neg_valid (scaleRat_valid (r := 4) (mul_valid (mul_valid latticeFrequency.property latticeFrequency.property)
      (mul_valid q.property (mul_valid j.property j.property)))))
    (integerReciprocalPowerRowSum_square_agreement z hz) (pairedReciprocalSquareSum_nome_quotient z hz)
  have hj := RepresentedReciprocal.mul_inverse (nomeDenominator q) (nome_upper_denominator_nonzero z hz)
  have hk := cotangentRationalMap_identity q
    (compose_outer_mem ((nomeRationalCotangentMap_full_domain z).mpr hz))
  have hF := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (integerReciprocalPowerRowSum z hz 4 (by omega)).property)
    (hright := (quarticRowRiccatiFormula z hz).property) hf
  have hS := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := vs)
    (hright := mul_valid (mul_valid q.property
      (add_valid (add_valid (ofQComplex_valid _) (scaleRat_valid (r := 4) q.property))
        (LocalODE.power_valid _ q.property 2))) (LocalODE.power_valid _ j.property 4)) hs
  have hP := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := (pairedPartialFractionMap.eval z hz).property)
    (hright := neg_valid (mul_valid latticeImaginaryUnit.property
      (mul_valid latticeFrequency.property (upperNomeCotangentMap.eval z hz).property))) hpi
  have hR := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := (integerReciprocalPowerRowSum z hz 2 (by omega)).property)
    (hright := neg_valid (scaleRat_valid (r := 4) (mul_valid (mul_valid latticeFrequency.property latticeFrequency.property)
      (mul_valid q.property (mul_valid j.property j.property))))) h2
  have hJ := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid (nomeDenominator q).property j.property)
    (hright := ofQComplex_valid _) hj
  have hK := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator q).property (upperNomeCotangentMap.eval z hz).property)
    (hright := add_valid (ofQComplex_valid _) q.property) hk
  have hC := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid latticeFrequency.property latticeFrequency.property)
    (hright := neg_valid pairedRiccatiCenterConstant.property) latticeFrequency_complex_square_identity
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (integerReciprocalPowerRowSum z hz 4 (by omega)).property)
    (hright := scaleRat_valid (r := (8/3:Rat)) (mul_valid (LocalODE.power_valid _ latticeFrequency.property 4) vs))
  let A := ComplexRawQuotient.ofRaw latticeFrequency.val latticeFrequency.property
  let I := ComplexRawQuotient.ofRaw latticeImaginaryUnit.val latticeImaginaryUnit.property
  let P := ComplexRawQuotient.ofRaw (pairedPartialFractionMap.eval z hz).val (pairedPartialFractionMap.eval z hz).property
  let C := ComplexRawQuotient.ofRaw pairedRiccatiCenterConstant.val pairedRiccatiCenterConstant.property
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  let J := ComplexRawQuotient.ofRaw j.val j.property
  let K := ComplexRawQuotient.ofRaw (upperNomeCotangentMap.eval z hz).val (upperNomeCotangentMap.eval z hz).property
  let R := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 2 (by omega)).val
    (integerReciprocalPowerRowSum z hz 2 (by omega)).property
  let F := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 4 (by omega)).val
    (integerReciprocalPowerRowSum z hz 4 (by omega)).property
  let S := ComplexRawQuotient.ofRaw (polynomialNomeMomentSum q r 3) vs
  change F=ComplexRawQuotient.scaleRat (1/3) (R*(ComplexRawQuotient.scaleRat 3 (P*P)-C)) at hF
  change P= -(I*(A*K)) at hP
  change R= -ComplexRawQuotient.scaleRat 4 ((A*A)*(Q*(J*J))) at hR
  change (1-Q)*J=1 at hJ
  change (1-Q)*K=1+Q at hK
  change A*A= -C at hC
  change S=(Q*(1+ComplexRawQuotient.scaleRat 4 Q+
    ComplexRawQuotient.ofRaw (LocalODE.power q.val 2) (LocalODE.power_valid _ q.property 2)))*
    ComplexRawQuotient.ofRaw (LocalODE.power j.val 4) (LocalODE.power_valid _ j.property 4) at hS
  rw [ScalarAlgebra.ofRaw_power,ScalarAlgebra.ofRaw_power] at hS
  change S=(Q*(1+ComplexRawQuotient.scaleRat 4 Q+Q^2))*J^4 at hS
  change F=ComplexRawQuotient.scaleRat (8/3)
    (ComplexRawQuotient.ofRaw (LocalODE.power latticeFrequency.val 4)
      (LocalODE.power_valid _ latticeFrequency.property 4)*S)
  rw [ScalarAlgebra.ofRaw_power]
  change F=ComplexRawQuotient.scaleRat (8/3) (A^4*S)
  have hI : I*I= -1 := latticeImaginaryUnit_square
  have sc3 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 3 x=(3:ScalarAlgebra.Value)*x := ScalarAlgebra.scale_natural 3 x
  have sc4 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 4 x=(4:ScalarAlgebra.Value)*x := ScalarAlgebra.scale_natural 4 x
  have sc8 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 8 x=(8:ScalarAlgebra.Value)*x := ScalarAlgebra.scale_natural 8 x
  rw [sc3] at hF
  rw [sc4] at hR hS
  generalize A=a,I=i,P=p,C=c,Q=q,J=j,K=k,R=v,F=f,S=s at hF hP hR hJ hK hC hS hI ⊢
  have hnum : v*((3:ScalarAlgebra.Value)*(p*p)-c)=(8:ScalarAlgebra.Value)*(a^4*s) := by grind only
  rw [hnum,← sc8] at hF
  rw [ComplexRawQuotient.scaleRat_scaleRat] at hF
  simpa only [show (1/3:Rat)*8=8/3 by decide +kernel] using hF

theorem integerReciprocalPowerRowSum_quartic_pi_fourier (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Rat) (hr : 0≤r) (hlocal : 16*r≤(1:Rat)/2) (hq : Small (nome.eval z hz).val r) :
    (integerReciprocalPowerRowSum z hz 4 (by omega)).val.Equiv
      (scaleRat (8/3) (mul (LocalODE.power geometricPiScalar.val 4)
        (polynomialNomeMomentSum (nome.eval z hz) r 3))) := by
  have hl : polynomialNomeMomentRatio r 3≤(1:Rat)/2 := by
    rw [polynomialNomeMomentRatio_three]; exact hlocal
  have vs := polynomialNomeMomentSum_valid (nome.eval z hz) r 3 hr hl hq
  have hp := LocalODE.power_congr _ _ latticeFrequency.property geometricPiScalar.property
    latticeFrequency_geometricPiScalar 4
  have hm := mul_equiv (LocalODE.power_valid _ latticeFrequency.property 4)
    (LocalODE.power_valid _ geometricPiScalar.property 4) vs vs hp (equiv_refl _ vs)
  exact equiv_trans (integerReciprocalPowerRowSum z hz 4 (by omega)).property
    (scaleRat_valid (r := (8/3:Rat)) (mul_valid (LocalODE.power_valid _ latticeFrequency.property 4) vs))
    (scaleRat_valid (r := (8/3:Rat)) (mul_valid (LocalODE.power_valid _ geometricPiScalar.property 4) vs))
    (integerReciprocalPowerRowSum_quartic_fourier z hz r hr hlocal hq)
    (scaleRat_equiv (r := (8/3:Rat)) hm)

end ComputableAnalysis.ModularForms
