import ComputableAnalysis.ModularForms.NomeMomentHigherReductions

/-! Exact quartic and quintic represented moment quotients. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

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

private theorem quotient_scale_4 (x : ComplexRawQuotient.Value) :
    ComplexRawQuotient.scaleRat 4 x=(4:ComplexRawQuotient.Value)*x :=
  ScalarAlgebra.scale_natural 4 x

private theorem quotient_scale_5 (x : ComplexRawQuotient.Value) :
    ComplexRawQuotient.scaleRat 5 x=(5:ComplexRawQuotient.Value)*x :=
  ScalarAlgebra.scale_natural 5 x

private theorem quotient_scale_6 (x : ComplexRawQuotient.Value) :
    ComplexRawQuotient.scaleRat 6 x=(6:ComplexRawQuotient.Value)*x :=
  ScalarAlgebra.scale_natural 6 x

private theorem quotient_scale_10 (x : ComplexRawQuotient.Value) :
    ComplexRawQuotient.scaleRat 10 x=(10:ComplexRawQuotient.Value)*x :=
  ScalarAlgebra.scale_natural 10 x

private theorem quotient_scale_11 (x : ComplexRawQuotient.Value) :
    ComplexRawQuotient.scaleRat 11 x=(11:ComplexRawQuotient.Value)*x :=
  ScalarAlgebra.scale_natural 11 x

private theorem quotient_scale_26 (x : ComplexRawQuotient.Value) :
    ComplexRawQuotient.scaleRat 26 x=(26:ComplexRawQuotient.Value)*x :=
  ScalarAlgebra.scale_natural 26 x

private theorem quotient_scale_66 (x : ComplexRawQuotient.Value) :
    ComplexRawQuotient.scaleRat 66 x=(66:ComplexRawQuotient.Value)*x :=
  ScalarAlgebra.scale_natural 66 x

theorem polynomialNomeMomentSum_four_quotient (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 32*r≤(1:Rat)/2) (hz : Small z.val r)
    (hn : NonzeroBoxSearch.Nonzero (nomeDenominator z)) :
    (polynomialNomeMomentSum z r 4).Equiv (mul (mul z.val (add (add (add (ofQComplex QComplex.one) (scaleRat 11 z.val)) (scaleRat 11 (LocalODE.power z.val 2))) (LocalODE.power z.val 3))) (LocalODE.power (RepresentedReciprocal.inverse (nomeDenominator z) hn).val 5)) := by
  have h0 : 2*r≤(1:Rat)/2 := by grind only
  have hl0 : polynomialNomeMomentRatio r 0≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_zero]; exact h0
  have h1 : 4*r≤(1:Rat)/2 := by grind only
  have hl1 : polynomialNomeMomentRatio r 1≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_one]; exact h1
  have h2 : 8*r≤(1:Rat)/2 := by grind only
  have hl2 : polynomialNomeMomentRatio r 2≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_two]; exact h2
  have h3 : 16*r≤(1:Rat)/2 := by grind only
  have hl3 : polynomialNomeMomentRatio r 3≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_three]; exact h3
  have h4 : 32*r≤(1:Rat)/2 := by grind only
  have hl4 : polynomialNomeMomentRatio r 4≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_four]; exact h4
  let j := RepresentedReciprocal.inverse (nomeDenominator z) hn
  have v0 := polynomialNomeMomentSum_valid z r 0 hr hl0 hz
  have v1 := polynomialNomeMomentSum_valid z r 1 hr hl1 hz
  have v2 := polynomialNomeMomentSum_valid z r 2 hr hl2 hz
  have v3 := polynomialNomeMomentSum_valid z r 3 hr hl3 hz
  have v4 := polynomialNomeMomentSum_valid z r 4 hr hl4 hz
  have vd := polynomialNomeDifferenceSum_valid z r 4 hr hl4 hz
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator z).property j.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (nomeDenominator z) hn)
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator z).property v4)
    (hright := add_valid vd (mul_valid (polynomialNomeCoefficient 4 0).property z.property))
    (polynomialNomeMoment_difference_identity z r 4 hr hl4 hz)
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := vd)
    (hright := (sub_valid (add_valid (sub_valid (scaleRat_valid (r := 4) v3) (scaleRat_valid (r := 6) v2)) (scaleRat_valid (r := 4) v1)) v0))
    (polynomialNomeDifferenceSum_degree_four z r hr hlocal hz)
  have hs0 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := v0) (hright := (mul_valid z.property j.property))
    (polynomialNomeMomentSum_zero_quotient z r hr h0 hz hn)
  have hs1 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := v1) (hright := (mul_valid z.property (mul_valid j.property j.property)))
    (polynomialNomeMomentSum_one_quotient z r hr h1 hz hn)
  have hs2 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := v2) (hright := (mul_valid (mul_valid z.property (add_valid (ofQComplex_valid _) z.property)) (LocalODE.power_valid _ j.property 3)))
    (polynomialNomeMomentSum_two_quotient z r hr h2 hz hn)
  have hs3 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := v3) (hright := (mul_valid (mul_valid z.property (add_valid (add_valid (ofQComplex_valid _) (scaleRat_valid (r := 4) z.property)) (LocalODE.power_valid _ z.property 2))) (LocalODE.power_valid _ j.property 4)))
    (polynomialNomeMomentSum_three_quotient z r hr h3 hz hn)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := v4) (hright := (mul_valid (mul_valid z.property (add_valid (add_valid (add_valid (ofQComplex_valid _) (scaleRat_valid (r := 11) z.property)) (scaleRat_valid (r := 11) (LocalODE.power_valid _ z.property 2))) (LocalODE.power_valid _ z.property 3))) (LocalODE.power_valid _ j.property 5)))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let J := ComplexRawQuotient.ofRaw j.val j.property
  let S0 := ComplexRawQuotient.ofRaw (polynomialNomeMomentSum z r 0) v0
  let S1 := ComplexRawQuotient.ofRaw (polynomialNomeMomentSum z r 1) v1
  let S2 := ComplexRawQuotient.ofRaw (polynomialNomeMomentSum z r 2) v2
  let S3 := ComplexRawQuotient.ofRaw (polynomialNomeMomentSum z r 3) v3
  let S4 := ComplexRawQuotient.ofRaw (polynomialNomeMomentSum z r 4) v4
  let D := ComplexRawQuotient.ofRaw (polynomialNomeDifferenceSum z r 4) vd
  change (1-Z)*J=1 at hi
  change (1-Z)*S4=D+ComplexRawQuotient.scaleRat ((0:Rat)^4) 1*Z at hs
  have hc : (0:Rat)^4=0 := by decide +kernel
  rw [hc,ComplexRawQuotient.scaleRat_zeroScalar] at hs
  change D=((((ComplexRawQuotient.scaleRat 4 S3)-(ComplexRawQuotient.scaleRat 6 S2))+(ComplexRawQuotient.scaleRat 4 S1))-S0) at hd
  simp only [quotient_scale_4,quotient_scale_5,quotient_scale_6,quotient_scale_10,quotient_scale_11,quotient_scale_26,quotient_scale_66] at hd
  change D=((((4*S3)-(6*S2))+(4*S1))-S0) at hd
  change S0=Z*J at hs0
  change S1=Z*(J*J) at hs1
  change S2=(Z*(1+Z))*ComplexRawQuotient.ofRaw (LocalODE.power j.val 3) (LocalODE.power_valid _ j.property 3) at hs2
  rw [ScalarAlgebra.ofRaw_power _ j.property] at hs2
  change S2=(Z*(1+Z))*J^3 at hs2
  change S3=(Z*((1+(ComplexRawQuotient.scaleRat 4 Z))+(ComplexRawQuotient.ofRaw (LocalODE.power z.val 2) (LocalODE.power_valid _ z.property 2))))*ComplexRawQuotient.ofRaw (LocalODE.power j.val 4) (LocalODE.power_valid _ j.property 4) at hs3
  simp only [ScalarAlgebra.ofRaw_power _ z.property,ScalarAlgebra.ofRaw_power _ j.property,quotient_scale_4,quotient_scale_5,quotient_scale_6,quotient_scale_10,quotient_scale_11,quotient_scale_26,quotient_scale_66] at hs3
  change S3=(Z*((1+(4*Z))+Z^2))*J^4 at hs3
  change S4=(Z*(((1+(ComplexRawQuotient.scaleRat 11 Z))+(ComplexRawQuotient.scaleRat 11 (ComplexRawQuotient.ofRaw (LocalODE.power z.val 2) (LocalODE.power_valid _ z.property 2))))+(ComplexRawQuotient.ofRaw (LocalODE.power z.val 3) (LocalODE.power_valid _ z.property 3))))*ComplexRawQuotient.ofRaw (LocalODE.power j.val 5) (LocalODE.power_valid _ j.property 5)
  simp only [ScalarAlgebra.ofRaw_power _ z.property,ScalarAlgebra.ofRaw_power _ j.property,quotient_scale_4,quotient_scale_5,quotient_scale_6,quotient_scale_10,quotient_scale_11,quotient_scale_26,quotient_scale_66]
  change S4=(Z*(((1+(11*Z))+(11*Z^2))+Z^3))*J^5
  have hsolve : S4=J*D := by
    generalize Z=z,J=j,S4=s,D=d at hi hs ⊢
    grind only
  have hnum : J*D=4*(Z*(1+4*Z+Z^2))*J^5-6*(Z*(1+Z))*J^4+4*Z*J^3-Z*J^2 := by
    rw [hd,hs0,hs1,hs2,hs3]
    generalize Z=z,J=j
    grind only
  have hp2 := inverse_power_factor Z J hi 3 2
  change J^2=(1-Z)^3*J^5 at hp2
  have hp3 := inverse_power_factor Z J hi 2 3
  change J^3=(1-Z)^2*J^5 at hp3
  have hp4 := inverse_power_factor Z J hi 1 4
  change J^4=(1-Z)^1*J^5 at hp4
  rw [hp2,hp3,hp4] at hnum
  rw [hsolve,hnum]
  generalize Z=z,J=j
  grind only

theorem polynomialNomeMomentSum_five_quotient (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 64*r≤(1:Rat)/2) (hz : Small z.val r)
    (hn : NonzeroBoxSearch.Nonzero (nomeDenominator z)) :
    (polynomialNomeMomentSum z r 5).Equiv (mul (mul z.val (add (add (add (add (ofQComplex QComplex.one) (scaleRat 26 z.val)) (scaleRat 66 (LocalODE.power z.val 2))) (scaleRat 26 (LocalODE.power z.val 3))) (LocalODE.power z.val 4))) (LocalODE.power (RepresentedReciprocal.inverse (nomeDenominator z) hn).val 6)) := by
  have h0 : 2*r≤(1:Rat)/2 := by grind only
  have hl0 : polynomialNomeMomentRatio r 0≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_zero]; exact h0
  have h1 : 4*r≤(1:Rat)/2 := by grind only
  have hl1 : polynomialNomeMomentRatio r 1≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_one]; exact h1
  have h2 : 8*r≤(1:Rat)/2 := by grind only
  have hl2 : polynomialNomeMomentRatio r 2≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_two]; exact h2
  have h3 : 16*r≤(1:Rat)/2 := by grind only
  have hl3 : polynomialNomeMomentRatio r 3≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_three]; exact h3
  have h4 : 32*r≤(1:Rat)/2 := by grind only
  have hl4 : polynomialNomeMomentRatio r 4≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_four]; exact h4
  have h5 : 64*r≤(1:Rat)/2 := by grind only
  have hl5 : polynomialNomeMomentRatio r 5≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_five]; exact h5
  let j := RepresentedReciprocal.inverse (nomeDenominator z) hn
  have v0 := polynomialNomeMomentSum_valid z r 0 hr hl0 hz
  have v1 := polynomialNomeMomentSum_valid z r 1 hr hl1 hz
  have v2 := polynomialNomeMomentSum_valid z r 2 hr hl2 hz
  have v3 := polynomialNomeMomentSum_valid z r 3 hr hl3 hz
  have v4 := polynomialNomeMomentSum_valid z r 4 hr hl4 hz
  have v5 := polynomialNomeMomentSum_valid z r 5 hr hl5 hz
  have vd := polynomialNomeDifferenceSum_valid z r 5 hr hl5 hz
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator z).property j.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (nomeDenominator z) hn)
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator z).property v5)
    (hright := add_valid vd (mul_valid (polynomialNomeCoefficient 5 0).property z.property))
    (polynomialNomeMoment_difference_identity z r 5 hr hl5 hz)
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := vd)
    (hright := (add_valid (sub_valid (add_valid (sub_valid (scaleRat_valid (r := 5) v4) (scaleRat_valid (r := 10) v3)) (scaleRat_valid (r := 10) v2)) (scaleRat_valid (r := 5) v1)) v0))
    (polynomialNomeDifferenceSum_degree_five z r hr hlocal hz)
  have hs0 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := v0) (hright := (mul_valid z.property j.property))
    (polynomialNomeMomentSum_zero_quotient z r hr h0 hz hn)
  have hs1 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := v1) (hright := (mul_valid z.property (mul_valid j.property j.property)))
    (polynomialNomeMomentSum_one_quotient z r hr h1 hz hn)
  have hs2 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := v2) (hright := (mul_valid (mul_valid z.property (add_valid (ofQComplex_valid _) z.property)) (LocalODE.power_valid _ j.property 3)))
    (polynomialNomeMomentSum_two_quotient z r hr h2 hz hn)
  have hs3 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := v3) (hright := (mul_valid (mul_valid z.property (add_valid (add_valid (ofQComplex_valid _) (scaleRat_valid (r := 4) z.property)) (LocalODE.power_valid _ z.property 2))) (LocalODE.power_valid _ j.property 4)))
    (polynomialNomeMomentSum_three_quotient z r hr h3 hz hn)
  have hs4 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := v4) (hright := (mul_valid (mul_valid z.property (add_valid (add_valid (add_valid (ofQComplex_valid _) (scaleRat_valid (r := 11) z.property)) (scaleRat_valid (r := 11) (LocalODE.power_valid _ z.property 2))) (LocalODE.power_valid _ z.property 3))) (LocalODE.power_valid _ j.property 5)))
    (polynomialNomeMomentSum_four_quotient z r hr h4 hz hn)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := v5) (hright := (mul_valid (mul_valid z.property (add_valid (add_valid (add_valid (add_valid (ofQComplex_valid _) (scaleRat_valid (r := 26) z.property)) (scaleRat_valid (r := 66) (LocalODE.power_valid _ z.property 2))) (scaleRat_valid (r := 26) (LocalODE.power_valid _ z.property 3))) (LocalODE.power_valid _ z.property 4))) (LocalODE.power_valid _ j.property 6)))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let J := ComplexRawQuotient.ofRaw j.val j.property
  let S0 := ComplexRawQuotient.ofRaw (polynomialNomeMomentSum z r 0) v0
  let S1 := ComplexRawQuotient.ofRaw (polynomialNomeMomentSum z r 1) v1
  let S2 := ComplexRawQuotient.ofRaw (polynomialNomeMomentSum z r 2) v2
  let S3 := ComplexRawQuotient.ofRaw (polynomialNomeMomentSum z r 3) v3
  let S4 := ComplexRawQuotient.ofRaw (polynomialNomeMomentSum z r 4) v4
  let S5 := ComplexRawQuotient.ofRaw (polynomialNomeMomentSum z r 5) v5
  let D := ComplexRawQuotient.ofRaw (polynomialNomeDifferenceSum z r 5) vd
  change (1-Z)*J=1 at hi
  change (1-Z)*S5=D+ComplexRawQuotient.scaleRat ((0:Rat)^5) 1*Z at hs
  have hc : (0:Rat)^5=0 := by decide +kernel
  rw [hc,ComplexRawQuotient.scaleRat_zeroScalar] at hs
  change D=(((((ComplexRawQuotient.scaleRat 5 S4)-(ComplexRawQuotient.scaleRat 10 S3))+(ComplexRawQuotient.scaleRat 10 S2))-(ComplexRawQuotient.scaleRat 5 S1))+S0) at hd
  simp only [quotient_scale_4,quotient_scale_5,quotient_scale_6,quotient_scale_10,quotient_scale_11,quotient_scale_26,quotient_scale_66] at hd
  change D=(((((5*S4)-(10*S3))+(10*S2))-(5*S1))+S0) at hd
  change S0=Z*J at hs0
  change S1=Z*(J*J) at hs1
  change S2=(Z*(1+Z))*ComplexRawQuotient.ofRaw (LocalODE.power j.val 3) (LocalODE.power_valid _ j.property 3) at hs2
  rw [ScalarAlgebra.ofRaw_power _ j.property] at hs2
  change S2=(Z*(1+Z))*J^3 at hs2
  change S3=(Z*((1+(ComplexRawQuotient.scaleRat 4 Z))+(ComplexRawQuotient.ofRaw (LocalODE.power z.val 2) (LocalODE.power_valid _ z.property 2))))*ComplexRawQuotient.ofRaw (LocalODE.power j.val 4) (LocalODE.power_valid _ j.property 4) at hs3
  simp only [ScalarAlgebra.ofRaw_power _ z.property,ScalarAlgebra.ofRaw_power _ j.property,quotient_scale_4,quotient_scale_5,quotient_scale_6,quotient_scale_10,quotient_scale_11,quotient_scale_26,quotient_scale_66] at hs3
  change S3=(Z*((1+(4*Z))+Z^2))*J^4 at hs3
  change S4=(Z*(((1+(ComplexRawQuotient.scaleRat 11 Z))+(ComplexRawQuotient.scaleRat 11 (ComplexRawQuotient.ofRaw (LocalODE.power z.val 2) (LocalODE.power_valid _ z.property 2))))+(ComplexRawQuotient.ofRaw (LocalODE.power z.val 3) (LocalODE.power_valid _ z.property 3))))*ComplexRawQuotient.ofRaw (LocalODE.power j.val 5) (LocalODE.power_valid _ j.property 5) at hs4
  simp only [ScalarAlgebra.ofRaw_power _ z.property,ScalarAlgebra.ofRaw_power _ j.property,quotient_scale_4,quotient_scale_5,quotient_scale_6,quotient_scale_10,quotient_scale_11,quotient_scale_26,quotient_scale_66] at hs4
  change S4=(Z*(((1+(11*Z))+(11*Z^2))+Z^3))*J^5 at hs4
  change S5=(Z*((((1+(ComplexRawQuotient.scaleRat 26 Z))+(ComplexRawQuotient.scaleRat 66 (ComplexRawQuotient.ofRaw (LocalODE.power z.val 2) (LocalODE.power_valid _ z.property 2))))+(ComplexRawQuotient.scaleRat 26 (ComplexRawQuotient.ofRaw (LocalODE.power z.val 3) (LocalODE.power_valid _ z.property 3))))+(ComplexRawQuotient.ofRaw (LocalODE.power z.val 4) (LocalODE.power_valid _ z.property 4))))*ComplexRawQuotient.ofRaw (LocalODE.power j.val 6) (LocalODE.power_valid _ j.property 6)
  simp only [ScalarAlgebra.ofRaw_power _ z.property,ScalarAlgebra.ofRaw_power _ j.property,quotient_scale_4,quotient_scale_5,quotient_scale_6,quotient_scale_10,quotient_scale_11,quotient_scale_26,quotient_scale_66]
  change S5=(Z*((((1+(26*Z))+(66*Z^2))+(26*Z^3))+Z^4))*J^6
  have hsolve : S5=J*D := by
    generalize Z=z,J=j,S5=s,D=d at hi hs ⊢
    grind only
  have hnum : J*D=5*(Z*(1+11*Z+11*Z^2+Z^3))*J^6-10*(Z*(1+4*Z+Z^2))*J^5+10*(Z*(1+Z))*J^4-5*Z*J^3+Z*J^2 := by
    rw [hd,hs0,hs1,hs2,hs3,hs4]
    generalize Z=z,J=j
    grind only
  have hp2 := inverse_power_factor Z J hi 4 2
  change J^2=(1-Z)^4*J^6 at hp2
  have hp3 := inverse_power_factor Z J hi 3 3
  change J^3=(1-Z)^3*J^6 at hp3
  have hp4 := inverse_power_factor Z J hi 2 4
  change J^4=(1-Z)^2*J^6 at hp4
  have hp5 := inverse_power_factor Z J hi 1 5
  change J^5=(1-Z)^1*J^6 at hp5
  rw [hp2,hp3,hp4,hp5] at hnum
  rw [hsolve,hnum]
  generalize Z=z,J=j
  grind only

end ComputableAnalysis.ModularForms
