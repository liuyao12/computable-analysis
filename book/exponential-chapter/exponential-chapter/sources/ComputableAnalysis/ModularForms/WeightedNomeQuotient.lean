import ComputableAnalysis.ModularForms.NomeDenominator
import ComputableAnalysis.ModularForms.WeightedNomePowers
import ComputableAnalysis.ModularForms.LambertPositivePowers

/-! Exact rational quotient for the constructed weighted nome series. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem weightedNome_boundary_bound (z : Scalar) (r : Rat) (hr : 0≤r)
    (hz : Small z.val r) (N : Nat) :
    Small (scaleRat (N:Rat) (LocalODE.power z.val (N+1))) (2*(2*r)*(4*r)^N) := by
  have h := LocalODE.small_scale (c := (N:Rat)) Rat.natCast_nonneg
    (LocalODE.power_small z.val z.property r hr hz (N+1))
  apply h.mono
  have hn : (N:Rat)≤(2:Rat)^N := Rat.le_trans
    (by exact_mod_cast (show N≤N+1 by omega)) (lambertIndex_bound N)
  have hp := Rat.pow_nonneg (a := 2*r) (n := N) (Rat.mul_nonneg (by decide) hr)
  have hm := Rat.mul_le_mul_of_nonneg_right hn
    (Rat.pow_nonneg (a := 2*r) (n := N+1) (Rat.mul_nonneg (by decide) hr))
  rw [Rat.pow_succ] at hm ⊢
  have he : (4*r)^N=(2:Rat)^N*(2*r)^N := by
    rw [show 4*r=2*(2*r) by grind only,LocalODE.rational_mul_pow]
  rw [he]
  have hb := Rat.mul_nonneg (Rat.pow_nonneg (n := N) (by decide : (0:Rat)≤2)) hp
  have hc := Rat.mul_nonneg hb (Rat.mul_nonneg (by decide : (0:Rat)≤2) hr)
  grind only

theorem weightedNomeSum_denominator_identity (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r) :
    (mul (sub (ofQComplex QComplex.one) z.val) (weightedNomeSum z r)).Equiv
      (lambertFactor z r) := by
  have htwo : 2*r≤(1:Rat)/2 := Rat.le_trans (by grind only) hlocal
  let d := sub (ofQComplex QComplex.one) z.val
  let s := weightedNomeSum z r
  let l := lambertFactor z r
  have vd : d.Valid := sub_valid (ofQComplex_valid _) z.property
  have vs := weightedNomeSum_valid z r hr hlocal hz
  have vl := lambertFactor_valid z r hr htwo hz
  have hone : Small (ofQComplex QComplex.one) 1 := by
    refine ⟨?_,?_,?_,?_⟩
    · intro n m; change (-1:Rat)≤1; decide +kernel
    · intro n m; change (1:Rat)≤1; decide +kernel
    · intro n m; change (-1:Rat)≤0; decide +kernel
    · intro n m; change (0:Rat)≤1; decide +kernel
  have hd : Small d (1+r) := SeriesLimitLaws.small_sub hone hz
  let e := fun N => (2*(1+r)*(4*(2*r)*(4*r)^N)+4*(2*r)^(N+1))+2*(2*r)*(4*r)^N
  have hsr := LocalODE.tail_bound_shrinks (2*r) (4*r)
    (Rat.mul_nonneg (by decide) hr) (Rat.mul_nonneg (by decide) hr) hlocal
  have he1 : ShrinksToZero (fun N => 2*(1+r)*(4*(2*r)*(4*r)^N)) :=
    SeriesLimitLaws.shrinks_scale _ hsr _ (Rat.mul_nonneg (by decide) (Rat.add_nonneg (by decide) hr))
  have he2 := lambertPositiveTail_shrinks r hr htwo
  have he3 : ShrinksToZero (fun N => 2*(2*r)*(4*r)^N) := by
    have ht := LocalODE.tail_bound_shrinks r (4*r) hr (Rat.mul_nonneg (by decide) hr) hlocal
    have he : (fun (N : Nat) => 2*(2*r)*(4*r)^N)=(fun (N : Nat) => 4*r*(4*r)^N) := by
      funext N; grind only
    rw [he]
    exact ht
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 e
    (RepresentedCauchySum.sum_shrinks _ _ (RepresentedCauchySum.sum_shrinks _ _ he1 he2) he3)
  intro N
  let p := weightedNomePrefix z N
  let g := lambertPositivePrefix z N
  let b := scaleRat (N:Rat) (LocalODE.power z.val (N+1))
  have vp := weightedNomePrefix_valid z N
  have vg := lambertPositivePrefix_valid z N
  have vb : b.Valid := scaleRat_valid (LocalODE.power_valid _ z.property (N+1))
  have hE : 0≤4*(2*r)*(4*r)^N := Rat.mul_nonneg
    (Rat.mul_nonneg (by decide) (Rat.mul_nonneg (by decide) hr))
    (Rat.pow_nonneg (n := N) (Rat.mul_nonneg (by decide) hr))
  have h1 := Small.mul vd (sub_valid vs vp) (Rat.add_nonneg (by decide) hr) hE hd
    (weightedNomeSum_close z r hr hlocal hz N)
  have h2 := SeriesLimitLaws.small_sub h1 (lambertPositivePrefix_close z r hr htwo hz N)
  have h3 := SeriesLimitLaws.small_sub h2 (weightedNome_boundary_bound z r hr hz N)
  have ht := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid vd vp)
    (hright := sub_valid vg vb) (weightedNomePrefix_telescoping z N)
  have hid : (sub (sub (mul d (sub s p)) (sub l g)) b).Equiv (sub (mul d s) l) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (sub_valid (mul_valid vd (sub_valid vs vp)) (sub_valid vl vg)) vb)
      (hright := sub_valid (mul_valid vd vs) vl)
    let D := ComplexRawQuotient.ofRaw d vd
    let S := ComplexRawQuotient.ofRaw s vs
    let P := ComplexRawQuotient.ofRaw p vp
    let L := ComplexRawQuotient.ofRaw l vl
    let G := ComplexRawQuotient.ofRaw g vg
    let B := ComplexRawQuotient.ofRaw b vb
    change D*P=G-B at ht
    change (D*(S-P)-(L-G))-B=D*S-L
    generalize D=a, S=c, P=f, L=k, G=m, B=j at ht ⊢
    grind only
  have h := Small.congr
    (sub_valid (sub_valid (mul_valid vd (sub_valid vs vp)) (sub_valid vl vg)) vb)
    (sub_valid (mul_valid vd vs) vl) hid h3
  simpa only [Rat.zero_add] using h

theorem weightedNomeSum_quotient (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r)
    (hn : NonzeroBoxSearch.Nonzero (nomeDenominator z)) :
    (weightedNomeSum z r).Equiv
      (mul z.val (mul (RepresentedReciprocal.inverse (nomeDenominator z) hn).val
        (RepresentedReciprocal.inverse (nomeDenominator z) hn).val)) := by
  have htwo : 2*r≤(1:Rat)/2 := Rat.le_trans (by grind only) hlocal
  let j := RepresentedReciprocal.inverse (nomeDenominator z) hn
  let g := nomeGeometricSum z r
  have vg := nomeGeometricSum_valid z r hr htwo hz
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator z).property j.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (nomeDenominator z) hn)
  have hg := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := vg) (hright := j.property)
    (equiv_symm (RepresentedReciprocal.inverse_unique (nomeDenominator z) hn ⟨g,vg⟩
      (nomeGeometricSum_inverse z r hr htwo hz)))
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator z).property (weightedNomeSum_valid z r hr hlocal hz))
    (hright := lambertFactor_valid z r hr htwo hz)
    (weightedNomeSum_denominator_identity z r hr hlocal hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := weightedNomeSum_valid z r hr hlocal hz)
    (hright := mul_valid z.property (mul_valid j.property j.property))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let J := ComplexRawQuotient.ofRaw j.val j.property
  let G := ComplexRawQuotient.ofRaw g vg
  let S := ComplexRawQuotient.ofRaw (weightedNomeSum z r) (weightedNomeSum_valid z r hr hlocal hz)
  change (1-Z)*J=1 at hi
  change G=J at hg
  change (1-Z)*S=Z*G at hs
  change S=Z*(J*J)
  generalize Z=a, J=b, G=c, S=d at hi hg hs ⊢
  grind only

end ComputableAnalysis.ModularForms
