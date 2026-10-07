import ComputableAnalysis.ModularForms.NomeMomentCubicReduction

/-! Exact cubic moment quotient from the constructed lower-degree reductions. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem polynomialNomeMomentSum_three_quotient (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 16*r≤(1:Rat)/2) (hz : Small z.val r)
    (hn : NonzeroBoxSearch.Nonzero (nomeDenominator z)) :
    (polynomialNomeMomentSum z r 3).Equiv
      (mul (mul z.val (add (add (ofQComplex QComplex.one) (scaleRat 4 z.val)) (LocalODE.power z.val 2)))
        (LocalODE.power (RepresentedReciprocal.inverse (nomeDenominator z) hn).val 4)) := by
  have h0 : 2*r≤(1:Rat)/2 := by grind only
  have h1 : 4*r≤(1:Rat)/2 := by grind only
  have h2 : 8*r≤(1:Rat)/2 := by grind only
  have hl0 : polynomialNomeMomentRatio r 0≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_zero]; exact h0
  have hl1 : polynomialNomeMomentRatio r 1≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_one]; exact h1
  have hl2 : polynomialNomeMomentRatio r 2≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_two]; exact h2
  have hl3 : polynomialNomeMomentRatio r 3≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_three]; exact hlocal
  let j := RepresentedReciprocal.inverse (nomeDenominator z) hn
  have v0 := polynomialNomeMomentSum_valid z r 0 hr hl0 hz
  have v1 := polynomialNomeMomentSum_valid z r 1 hr hl1 hz
  have v2 := polynomialNomeMomentSum_valid z r 2 hr hl2 hz
  have v3 := polynomialNomeMomentSum_valid z r 3 hr hl3 hz
  have vd := polynomialNomeDifferenceSum_valid z r 3 hr hl3 hz
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator z).property j.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (nomeDenominator z) hn)
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator z).property v3)
    (hright := add_valid vd (mul_valid (polynomialNomeCoefficient 3 0).property z.property))
    (polynomialNomeMoment_difference_identity z r 3 hr hl3 hz)
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := vd)
    (hright := add_valid (sub_valid (scaleRat_valid (r := 3) v2) (scaleRat_valid (r := 3) v1)) v0)
    (polynomialNomeDifferenceSum_degree_three z r hr hlocal hz)
  have hs0 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := v0) (hright := mul_valid z.property j.property)
    (polynomialNomeMomentSum_zero_quotient z r hr h0 hz hn)
  have hs1 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := v1)
    (hright := mul_valid z.property (mul_valid j.property j.property))
    (polynomialNomeMomentSum_one_quotient z r hr h1 hz hn)
  have hs2 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := v2)
    (hright := mul_valid (mul_valid z.property (add_valid (ofQComplex_valid _) z.property))
      (LocalODE.power_valid _ j.property 3))
    (polynomialNomeMomentSum_two_quotient z r hr h2 hz hn)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := v3)
    (hright := mul_valid (mul_valid z.property
      (add_valid (add_valid (ofQComplex_valid _) (scaleRat_valid (r := 4) z.property))
        (LocalODE.power_valid _ z.property 2))) (LocalODE.power_valid _ j.property 4))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let J := ComplexRawQuotient.ofRaw j.val j.property
  let S0 := ComplexRawQuotient.ofRaw (polynomialNomeMomentSum z r 0) v0
  let S1 := ComplexRawQuotient.ofRaw (polynomialNomeMomentSum z r 1) v1
  let S2 := ComplexRawQuotient.ofRaw (polynomialNomeMomentSum z r 2) v2
  let S3 := ComplexRawQuotient.ofRaw (polynomialNomeMomentSum z r 3) v3
  let D := ComplexRawQuotient.ofRaw (polynomialNomeDifferenceSum z r 3) vd
  change (1-Z)*J=1 at hi
  change (1-Z)*S3=D+ComplexRawQuotient.scaleRat ((0:Rat)^3) 1*Z at hs
  have hc : (0:Rat)^3=0 := by decide +kernel
  rw [hc,ComplexRawQuotient.scaleRat_zeroScalar] at hs
  change D=(ComplexRawQuotient.scaleRat 3 S2-ComplexRawQuotient.scaleRat 3 S1)+S0 at hd
  have hthree (X : ComplexRawQuotient.Value) : ComplexRawQuotient.scaleRat 3 X=X+X+X := by
    have hc : (3:Rat)=1+1+1 := by decide +kernel
    rw [hc,←ComplexRawQuotient.add_scaleRat,←ComplexRawQuotient.add_scaleRat,ComplexRawQuotient.scaleRat_one]
  rw [hthree,hthree] at hd
  change S0=Z*J at hs0
  change S1=Z*(J*J) at hs1
  change S2=(Z*(1+Z))*ComplexRawQuotient.ofRaw (LocalODE.power j.val 3) (LocalODE.power_valid _ j.property 3) at hs2
  rw [ScalarAlgebra.ofRaw_power _ j.property] at hs2
  change S3=(Z*((1+ComplexRawQuotient.scaleRat 4 Z)+
    ComplexRawQuotient.ofRaw (LocalODE.power z.val 2) (LocalODE.power_valid _ z.property 2)))*
    ComplexRawQuotient.ofRaw (LocalODE.power j.val 4) (LocalODE.power_valid _ j.property 4)
  rw [ScalarAlgebra.ofRaw_power _ z.property,ScalarAlgebra.ofRaw_power _ j.property]
  have hfour : ComplexRawQuotient.scaleRat 4 Z=Z+Z+Z+Z := by
    have hc : (4:Rat)=1+1+1+1 := by decide +kernel
    rw [hc,←ComplexRawQuotient.add_scaleRat,←ComplexRawQuotient.add_scaleRat,
      ←ComplexRawQuotient.add_scaleRat,ComplexRawQuotient.scaleRat_one]
  rw [hfour]
  change S2=(Z*(1+Z))*J^3 at hs2
  change S3=(Z*((1+(Z+Z+Z+Z))+Z^2))*J^4
  generalize Z=z,J=j,S0=a,S1=b,S2=c,S3=e,D=d at hi hs hd hs0 hs1 hs2 ⊢
  grind only

end ComputableAnalysis.ModularForms
