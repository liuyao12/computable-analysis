import ComputableAnalysis.ModularForms.NomeGeometricSeries

/-! Exact reciprocal identity for the actual convergent geometric nome sum. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem nomeGeometricSum_inverse (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 2*r≤(1:Rat)/2) (hz : Small z.val r) :
    (mul (sub (ofQComplex QComplex.one) z.val) (nomeGeometricSum z r)).Equiv
      (ofQComplex QComplex.one) := by
  let f := sub (ofQComplex QComplex.one) z.val
  have hf : f.Valid := sub_valid (ofQComplex_valid _) z.property
  have hs := nomeGeometricSum_valid z r hr hlocal hz
  have hone : Small (ofQComplex QComplex.one) 1 := by
    refine ⟨?_,?_,?_,?_⟩
    · intro n m; change (-1:Rat) ≤ 1; decide
    · intro n m; change (1:Rat) ≤ 1; decide
    · intro n m; change (-1:Rat) ≤ 0; decide
    · intro n m; change (0:Rat) ≤ 1; decide
  have hfb : Small f (1+r) := SeriesLimitLaws.small_sub hone hz
  let C := 8*(1+r)+1
  have hD : 0≤1+r := Rat.add_nonneg (by decide) hr
  have hC : 0≤C := Rat.add_nonneg (Rat.mul_nonneg (by decide) hD) (by decide)
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 (fun N => 4*C*(2*r)^N)
    (LocalODE.tail_bound_shrinks C (2*r) hC (Rat.mul_nonneg (by decide) hr) hlocal)
  intro N
  have he := nomeGeometricSum_close z r hr hlocal hz N
  have hE : 0≤4*(2*r)^N := Rat.mul_nonneg (by decide)
    (Rat.pow_nonneg (n := N) (Rat.mul_nonneg (by decide) hr))
  have hb := Small.mul hf (sub_valid hs (nomeGeometricPrefix_valid z N)) hD hE hfb he
  have hp := SeriesLimitLaws.small_neg (LocalODE.power_small z.val z.property r hr hz N)
  have hsum := LocalODE.small_add hb hp
  have hid : (sub (mul f (nomeGeometricSum z r)) (ofQComplex QComplex.one)).Equiv
      (add (mul f (sub (nomeGeometricSum z r) (nomeGeometricPrefix z N)))
        (neg (LocalODE.power z.val N))) := by
    have ht := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := mul_valid hf (nomeGeometricPrefix_valid z N))
      (hright := sub_valid (ofQComplex_valid _) (LocalODE.power_valid _ z.property N))
      (nomeGeometricPrefix_telescoping z N)
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (mul_valid hf hs) (ofQComplex_valid _))
      (hright := add_valid (mul_valid hf (sub_valid hs (nomeGeometricPrefix_valid z N)))
        (neg_valid (LocalODE.power_valid _ z.property N)))
    let F := ComplexRawQuotient.ofRaw f hf
    let S := ComplexRawQuotient.ofRaw (nomeGeometricSum z r) hs
    let P := ComplexRawQuotient.ofRaw (nomeGeometricPrefix z N) (nomeGeometricPrefix_valid z N)
    let Q := ComplexRawQuotient.ofRaw (LocalODE.power z.val N) (LocalODE.power_valid _ z.property N)
    change F*P=1-Q at ht
    change F*S-1=F*(S-P)+ -Q
    grind only
  have hfinal := Small.congr
    (add_valid (mul_valid hf (sub_valid hs (nomeGeometricPrefix_valid z N)))
      (neg_valid (LocalODE.power_valid _ z.property N)))
    (sub_valid (mul_valid hf hs) (ofQComplex_valid _)) (equiv_symm hid) hsum
  apply hfinal.mono
  have hpow := Rat.pow_nonneg (n := N) (Rat.mul_nonneg (by decide : (0:Rat)≤2) hr)
  have hmul := Rat.mul_nonneg hC hpow
  dsimp [C] at *
  grind only

end ComputableAnalysis.ModularForms
