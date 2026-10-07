import ComputableAnalysis.ModularForms.NomeMomentPrefixLinearity
import ComputableAnalysis.ModularForms.NomeMomentZeroQuotient
import ComputableAnalysis.ModularForms.PolynomialNomeDifferenceLimit

/-! Actual quadratic difference series reduces to the two base moments. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem polynomialNomeMomentRatio_two (r : Rat) : polynomialNomeMomentRatio r 2=8*r := by
  simp only [polynomialNomeMomentRatio,Rat.pow_succ,Rat.pow_zero,Rat.one_mul]
  grind only

theorem polynomialNomeDifferenceSum_degree_two (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 8*r≤(1:Rat)/2) (hz : Small z.val r) :
    (polynomialNomeDifferenceSum z r 2).Equiv
      (sub (scaleRat 2 (polynomialNomeMomentSum z r 1)) (polynomialNomeMomentSum z r 0)) := by
  have hl0 : polynomialNomeMomentRatio r 0≤(1:Rat)/2 := by
    rw [polynomialNomeMomentRatio_zero]; grind only
  have hl1 : polynomialNomeMomentRatio r 1≤(1:Rat)/2 := by
    rw [polynomialNomeMomentRatio_one]; grind only
  have hl2 : polynomialNomeMomentRatio r 2≤(1:Rat)/2 := by
    rw [polynomialNomeMomentRatio_two]; exact hlocal
  let s := polynomialNomeMomentSum z r 1
  let t := polynomialNomeMomentSum z r 0
  let d := polynomialNomeDifferenceSum z r 2
  have vs := polynomialNomeMomentSum_valid z r 1 hr hl1 hz
  have vt := polynomialNomeMomentSum_valid z r 0 hr hl0 hz
  have vd := polynomialNomeDifferenceSum_valid z r 2 hr hl2 hz
  let e := fun (k N : Nat) => 4*r*(polynomialNomeMomentRatio r k)^N
  have he (k : Nat) (hk : polynomialNomeMomentRatio r k≤(1:Rat)/2) : ShrinksToZero (e k) :=
    LocalODE.tail_bound_shrinks r _ hr (polynomialNomeMomentRatio_nonneg r k hr) hk
  have hen (k N : Nat) : 0≤e k N := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hr)
    (Rat.pow_nonneg (polynomialNomeMomentRatio_nonneg r k hr))
  let p := fun N => sub (scaleRat 2 (polynomialNomeMomentPrefix z 1 N)) (polynomialNomeMomentPrefix z 0 N)
  have vp N : (p N).Valid := sub_valid (scaleRat_valid (polynomialNomeMomentPrefix_valid z 1 N))
    (polynomialNomeMomentPrefix_valid z 0 N)
  have htail := RepresentedCauchySum.sum_shrinks _ _ (he 2 hl2)
    (RepresentedCauchySum.sum_shrinks _ _ (SeriesLimitLaws.shrinks_scale (e 1) (he 1 hl1) 2 (by decide)) (he 0 hl0))
  apply RepresentedCauchySum.unique p vp (fun N => e 2 N+(2*e 1 N+e 0 N)) htail
    d (sub (scaleRat 2 s) t) vd (sub_valid (scaleRat_valid vs) vt)
  · intro N
    have h := Small.congr
      (sub_valid vd (ScalarSeries.block_valid _ (polynomialNomeDifferenceTerm_valid z 2) 0 N))
      (sub_valid vd (vp N))
      (FunctionTheory.sub_congr (equiv_refl _ vd) (polynomialNomeDifferencePrefix_degree_two z N))
      (polynomialNomeDifferenceSum_close z r 2 hr hl2 hz N)
    exact h.mono (by have h1 := hen 1 N; have h0 := hen 0 N; grind only)
  · intro N
    let a := polynomialNomeMomentPrefix z 1 N
    let b := polynomialNomeMomentPrefix z 0 N
    have va := polynomialNomeMomentPrefix_valid z 1 N
    have vb := polynomialNomeMomentPrefix_valid z 0 N
    have h := SeriesLimitLaws.small_sub
      (LocalODE.small_scale (c := 2) (by decide) (polynomialNomeMomentSum_close z r 1 hr hl1 hz N))
      (polynomialNomeMomentSum_close z r 0 hr hl0 hz N)
    have hid : (sub (scaleRat 2 (sub s a)) (sub t b)).Equiv
        (sub (sub (scaleRat 2 s) t) (p N)) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := sub_valid (scaleRat_valid (sub_valid vs va)) (sub_valid vt vb))
        (hright := sub_valid (sub_valid (scaleRat_valid vs) vt) (vp N))
      let S := ComplexRawQuotient.ofRaw s vs
      let T := ComplexRawQuotient.ofRaw t vt
      let A := ComplexRawQuotient.ofRaw a va
      let B := ComplexRawQuotient.ofRaw b vb
      change ComplexRawQuotient.scaleRat 2 (S-A)-(T-B)=
        (ComplexRawQuotient.scaleRat 2 S-T)-(ComplexRawQuotient.scaleRat 2 A-B)
      have htwo (X : ComplexRawQuotient.Value) : ComplexRawQuotient.scaleRat 2 X=X+X := by
        have hc : (2:Rat)=1+1 := by decide +kernel
        rw [hc,←ComplexRawQuotient.add_scaleRat,ComplexRawQuotient.scaleRat_one]
      rw [htwo,htwo,htwo]
      generalize S=s,T=t,A=a,B=b
      grind only
    have h' := Small.congr (sub_valid (scaleRat_valid (sub_valid vs va)) (sub_valid vt vb))
      (sub_valid (sub_valid (scaleRat_valid vs) vt) (vp N)) hid h
    exact h'.mono (by have h2 := hen 2 N; grind only)

theorem polynomialNomeMomentSum_two_quotient (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 8*r≤(1:Rat)/2) (hz : Small z.val r)
    (hn : NonzeroBoxSearch.Nonzero (nomeDenominator z)) :
    (polynomialNomeMomentSum z r 2).Equiv
      (mul (mul z.val (add (ofQComplex QComplex.one) z.val))
        (LocalODE.power (RepresentedReciprocal.inverse (nomeDenominator z) hn).val 3)) := by
  have h0 : 2*r≤(1:Rat)/2 := by grind only
  have h1 : 4*r≤(1:Rat)/2 := by grind only
  have hl0 : polynomialNomeMomentRatio r 0≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_zero]; exact h0
  have hl1 : polynomialNomeMomentRatio r 1≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_one]; exact h1
  have hl2 : polynomialNomeMomentRatio r 2≤(1:Rat)/2 := by rw [polynomialNomeMomentRatio_two]; exact hlocal
  let j := RepresentedReciprocal.inverse (nomeDenominator z) hn
  have v0 := polynomialNomeMomentSum_valid z r 0 hr hl0 hz
  have v1 := polynomialNomeMomentSum_valid z r 1 hr hl1 hz
  have v2 := polynomialNomeMomentSum_valid z r 2 hr hl2 hz
  have vd := polynomialNomeDifferenceSum_valid z r 2 hr hl2 hz
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator z).property j.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (nomeDenominator z) hn)
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator z).property v2)
    (hright := add_valid vd (mul_valid (polynomialNomeCoefficient 2 0).property z.property))
    (polynomialNomeMoment_difference_identity z r 2 hr hl2 hz)
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := vd)
    (hright := sub_valid (scaleRat_valid (r := 2) v1) v0)
    (polynomialNomeDifferenceSum_degree_two z r hr hlocal hz)
  have hs0 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := v0) (hright := mul_valid z.property j.property)
    (polynomialNomeMomentSum_zero_quotient z r hr h0 hz hn)
  have hs1 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := v1)
    (hright := mul_valid z.property (mul_valid j.property j.property))
    (polynomialNomeMomentSum_one_quotient z r hr h1 hz hn)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := v2)
    (hright := mul_valid (mul_valid z.property (add_valid (ofQComplex_valid _) z.property))
      (LocalODE.power_valid _ j.property 3))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let J := ComplexRawQuotient.ofRaw j.val j.property
  let S0 := ComplexRawQuotient.ofRaw (polynomialNomeMomentSum z r 0) v0
  let S1 := ComplexRawQuotient.ofRaw (polynomialNomeMomentSum z r 1) v1
  let S2 := ComplexRawQuotient.ofRaw (polynomialNomeMomentSum z r 2) v2
  let D := ComplexRawQuotient.ofRaw (polynomialNomeDifferenceSum z r 2) vd
  change (1-Z)*J=1 at hi
  change (1-Z)*S2=D+ComplexRawQuotient.scaleRat ((0:Rat)^2) 1*Z at hs
  have hc : (0:Rat)^2=0 := by decide +kernel
  rw [hc,ComplexRawQuotient.scaleRat_zeroScalar] at hs
  change D=ComplexRawQuotient.scaleRat 2 S1-S0 at hd
  have htwo : ComplexRawQuotient.scaleRat 2 S1=S1+S1 := by
    have hc : (2:Rat)=1+1 := by decide +kernel
    rw [hc,←ComplexRawQuotient.add_scaleRat,ComplexRawQuotient.scaleRat_one]
  rw [htwo] at hd
  change S0=Z*J at hs0
  change S1=Z*(J*J) at hs1
  change S2=(Z*(1+Z))*ComplexRawQuotient.ofRaw (LocalODE.power j.val 3) (LocalODE.power_valid _ j.property 3)
  rw [ScalarAlgebra.ofRaw_power _ j.property]
  change S2=(Z*(1+Z))*J^3
  generalize Z=z,J=j,S0=a,S1=b,S2=c,D=d at hi hs hd hs0 hs1 ⊢
  grind only

end ComputableAnalysis.ModularForms
