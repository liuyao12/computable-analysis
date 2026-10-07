import ComputableAnalysis.ModularForms.IntegerPowerRowSextic
import ComputableAnalysis.ModularForms.NomeMomentHigherQuotients
import ComputableAnalysis.ModularForms.LatticePartialFractionNome

/-! Exact Fourier identity of the actual sextic row and quintic nome moment. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private theorem inverse_power_factor (z j : ComplexRawQuotient.Value)
    (hi : (1-z)*j=1) (m n : Nat) : j^n=(1-z)^m*j^(n+m) := by
  induction m with
  | zero => simp only [Nat.add_zero]; change j^n=1*j^n; grind only
  | succ m ih =>
    have h : j^n=((1-z)^m*j^(n+m))*((1-z)*j)  := by
      rw [hi]
      calc
        _ = (1-z)^m*j^(n+m) := ih
        _ = _ := by grind only
    rw [show n+(m+1)=(n+m)+1 by omega]
    change j^n=((1-z)^m*(1-z))*(j^(n+m)*j)
    calc
      _ = ((1-z)^m*j^(n+m))*((1-z)*j) := h
      _ = _ := by grind only

private theorem nome_sextic_algebra (a i p c q j k v s : ScalarAlgebra.Value)
    (hp : p= -(i*(a*k))) (hi : i*i= -1) (hc : a*a= -c)
    (hj : (1-q)*j=1) (hk : (1-q)*k=1+q)
    (hv : v= -((4:ScalarAlgebra.Value)*((a*a)*(q*(j*j)))))
    (hs : s=(q*((((1+(26:ScalarAlgebra.Value)*q)+(66:ScalarAlgebra.Value)*q^2)+
      (26:ScalarAlgebra.Value)*q^3)+q^4))*j^6) :
    v*((15*p^4-15*(c*(p*p)))+2*(c*c))= -((8:ScalarAlgebra.Value)*(a^6*s)) := by
  have kformula : k=(1+q)*j := by
    clear hp hi hc hv hs
    grind only
  have cformula : c= -(a*a) := by
    clear hp hi hj hk hv hs kformula
    grind only
  have p2 : p*p= -(a*a)*(k*k) := by
    rw [hp]
    clear hp hc hj hk hv hs kformula cformula
    grind only
  have p4 : p^4=a^4*k^4 := by
    have hpowers (x : ScalarAlgebra.Value) : x^4=(x*x)*(x*x) := by
      clear hp hi hc hj hk hv hs kformula cformula p2
      grind only
    rw [hpowers p,hpowers a,hpowers k,p2]
    clear hp hi hc hj hk hv hs kformula cformula
    grind only
  rw [p4,p2,cformula,kformula,hv,hs]
  clear hp hi hc hk hv hs kformula cformula p2 p4
  have j2 := inverse_power_factor q j hj 4 2
  have j4 := inverse_power_factor q j hj 2 4
  have common :
      -((4:ScalarAlgebra.Value)*((a*a)*(q*(j*j))))*
        ((15*(a^4*((1+q)*j)^4)-15*((-(a*a))*(-(a*a)*(((1+q)*j)*((1+q)*j)))))+
          2*((-(a*a))*(-(a*a)))) =
      -(4*a^6*q)*((15*(1+q)^4)*j^6-15*(1+q)^2*j^4+2*j^2) := by
    clear hj j2 j4
    grind only
  rw [common,j2,j4]
  clear hj j2 j4 common
  grind only

theorem integerReciprocalPowerRowSum_sextic_fourier (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Rat) (hr : 0≤r) (hlocal : 64*r≤(1:Rat)/2) (hq : Small (nome.eval z hz).val r) :
    (integerReciprocalPowerRowSum z hz 6 (by omega)).val.Equiv
      (scaleRat (-8/15) (mul (LocalODE.power latticeFrequency.val 6)
        (polynomialNomeMomentSum (nome.eval z hz) r 5))) := by
  let q := nome.eval z hz
  let j := RepresentedReciprocal.inverse (nomeDenominator q) (nome_upper_denominator_nonzero z hz)
  have hl : polynomialNomeMomentRatio r 5≤(1:Rat)/2 := by
    rw [polynomialNomeMomentRatio_five]; exact hlocal
  have vs := polynomialNomeMomentSum_valid q r 5 hr hl hq
  have hf := integerReciprocalPowerRowSum_sextic_riccati z hz
  have hs := polynomialNomeMomentSum_five_quotient q r hr hlocal hq (nome_upper_denominator_nonzero z hz)
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
    (hleft := (integerReciprocalPowerRowSum z hz 6 (by omega)).property)
    (hright := (sexticRowRiccatiFormula z hz).property) hf
  have hS := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := vs)
    (hright := mul_valid (mul_valid q.property
      (add_valid (add_valid (add_valid (add_valid (ofQComplex_valid _) (scaleRat_valid (r := 26) q.property))
        (scaleRat_valid (r := 66) (LocalODE.power_valid _ q.property 2)))
        (scaleRat_valid (r := 26) (LocalODE.power_valid _ q.property 3)))
        (LocalODE.power_valid _ q.property 4))) (LocalODE.power_valid _ j.property 6)) hs
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
    (hleft := (integerReciprocalPowerRowSum z hz 6 (by omega)).property)
    (hright := scaleRat_valid (r := (-8/15:Rat)) (mul_valid (LocalODE.power_valid _ latticeFrequency.property 6) vs))
  let A := ComplexRawQuotient.ofRaw latticeFrequency.val latticeFrequency.property
  let I := ComplexRawQuotient.ofRaw latticeImaginaryUnit.val latticeImaginaryUnit.property
  let P := ComplexRawQuotient.ofRaw (pairedPartialFractionMap.eval z hz).val (pairedPartialFractionMap.eval z hz).property
  let C := ComplexRawQuotient.ofRaw pairedRiccatiCenterConstant.val pairedRiccatiCenterConstant.property
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  let J := ComplexRawQuotient.ofRaw j.val j.property
  let K := ComplexRawQuotient.ofRaw (upperNomeCotangentMap.eval z hz).val (upperNomeCotangentMap.eval z hz).property
  let R := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 2 (by omega)).val
    (integerReciprocalPowerRowSum z hz 2 (by omega)).property
  let F := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 6 (by omega)).val
    (integerReciprocalPowerRowSum z hz 6 (by omega)).property
  let S := ComplexRawQuotient.ofRaw (polynomialNomeMomentSum q r 5) vs
  change F=ComplexRawQuotient.scaleRat (1/15) (R*
    ((ComplexRawQuotient.scaleRat 15
      (ComplexRawQuotient.ofRaw (LocalODE.power (pairedPartialFractionMap.eval z hz).val 4)
        (LocalODE.power_valid _ (pairedPartialFractionMap.eval z hz).property 4))-
      ComplexRawQuotient.scaleRat 15 (C*(P*P)))+ComplexRawQuotient.scaleRat 2 (C*C))) at hF
  rw [ScalarAlgebra.ofRaw_power] at hF
  change F=ComplexRawQuotient.scaleRat (1/15) (R*
    ((ComplexRawQuotient.scaleRat 15 (P^4)-ComplexRawQuotient.scaleRat 15 (C*(P*P)))+
      ComplexRawQuotient.scaleRat 2 (C*C))) at hF
  change P= -(I*(A*K)) at hP
  change R= -ComplexRawQuotient.scaleRat 4 ((A*A)*(Q*(J*J))) at hR
  change (1-Q)*J=1 at hJ
  change (1-Q)*K=1+Q at hK
  change A*A= -C at hC
  change S=(Q*((((1+ComplexRawQuotient.scaleRat 26 Q)+ComplexRawQuotient.scaleRat 66
    (ComplexRawQuotient.ofRaw (LocalODE.power q.val 2) (LocalODE.power_valid _ q.property 2)))+
    ComplexRawQuotient.scaleRat 26
      (ComplexRawQuotient.ofRaw (LocalODE.power q.val 3) (LocalODE.power_valid _ q.property 3)))+
    ComplexRawQuotient.ofRaw (LocalODE.power q.val 4) (LocalODE.power_valid _ q.property 4)))*
    ComplexRawQuotient.ofRaw (LocalODE.power j.val 6) (LocalODE.power_valid _ j.property 6) at hS
  rw [ScalarAlgebra.ofRaw_power,ScalarAlgebra.ofRaw_power,ScalarAlgebra.ofRaw_power,ScalarAlgebra.ofRaw_power] at hS
  change S=(Q*((((1+ComplexRawQuotient.scaleRat 26 Q)+ComplexRawQuotient.scaleRat 66 (Q^2))+
    ComplexRawQuotient.scaleRat 26 (Q^3))+Q^4))*J^6 at hS
  change F=ComplexRawQuotient.scaleRat (-8/15)
    (ComplexRawQuotient.ofRaw (LocalODE.power latticeFrequency.val 6)
      (LocalODE.power_valid _ latticeFrequency.property 6)*S)
  rw [ScalarAlgebra.ofRaw_power]
  change F=ComplexRawQuotient.scaleRat (-8/15) (A^6*S)
  have hI : I*I= -1 := latticeImaginaryUnit_square
  have sc2 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 2 x=(2:ScalarAlgebra.Value)*x := ScalarAlgebra.scale_natural 2 x
  have sc4 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 4 x=(4:ScalarAlgebra.Value)*x := ScalarAlgebra.scale_natural 4 x
  have sc8 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 8 x=(8:ScalarAlgebra.Value)*x := ScalarAlgebra.scale_natural 8 x
  have sc15 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 15 x=(15:ScalarAlgebra.Value)*x := ScalarAlgebra.scale_natural 15 x
  have sc26 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 26 x=(26:ScalarAlgebra.Value)*x := ScalarAlgebra.scale_natural 26 x
  have sc66 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 66 x=(66:ScalarAlgebra.Value)*x := ScalarAlgebra.scale_natural 66 x
  rw [sc15,sc15,sc2] at hF
  rw [sc4] at hR
  rw [sc26,sc26,sc66] at hS
  generalize A=a,I=i,P=p,C=c,Q=q,J=j,K=k,R=v,F=f,S=s at hF hP hR hJ hK hC hS hI ⊢
  have hnum : v*(((15:ScalarAlgebra.Value)*p^4-15*(c*(p*p)))+2*(c*c))=
      -((8:ScalarAlgebra.Value)*(a^6*s)) := nome_sextic_algebra a i p c q j k v s hP hI hC hJ hK hR hS
  rw [hnum,← sc8,ComplexRawQuotient.neg_scaleRat] at hF
  rw [ComplexRawQuotient.scaleRat_scaleRat] at hF
  simpa only [show (1/15:Rat)*(-8)= -8/15 by decide +kernel] using hF

theorem integerReciprocalPowerRowSum_sextic_pi_fourier (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Rat) (hr : 0≤r) (hlocal : 64*r≤(1:Rat)/2) (hq : Small (nome.eval z hz).val r) :
    (integerReciprocalPowerRowSum z hz 6 (by omega)).val.Equiv
      (scaleRat (-8/15) (mul (LocalODE.power geometricPiScalar.val 6)
        (polynomialNomeMomentSum (nome.eval z hz) r 5))) := by
  have hl : polynomialNomeMomentRatio r 5≤(1:Rat)/2 := by
    rw [polynomialNomeMomentRatio_five]; exact hlocal
  have vs := polynomialNomeMomentSum_valid (nome.eval z hz) r 5 hr hl hq
  have hp := LocalODE.power_congr _ _ latticeFrequency.property geometricPiScalar.property
    latticeFrequency_geometricPiScalar 6
  have hm := mul_equiv (LocalODE.power_valid _ latticeFrequency.property 6)
    (LocalODE.power_valid _ geometricPiScalar.property 6) vs vs hp (equiv_refl _ vs)
  exact equiv_trans (integerReciprocalPowerRowSum z hz 6 (by omega)).property
    (scaleRat_valid (r := (-8/15:Rat)) (mul_valid (LocalODE.power_valid _ latticeFrequency.property 6) vs))
    (scaleRat_valid (r := (-8/15:Rat)) (mul_valid (LocalODE.power_valid _ geometricPiScalar.property 6) vs))
    (integerReciprocalPowerRowSum_sextic_fourier z hz r hr hlocal hq)
    (scaleRat_equiv (r := (-8/15:Rat)) hm)

end ComputableAnalysis.ModularForms
