import ComputableAnalysis.ModularForms.PairedDivisionTwiceDifferentiable

/-! Summable differences of the actual second-derivative terms. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedDivisionSecondDerivativeTerm_difference_bound (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (n : Nat) :
    Small (sub (pairedDivisionSecondDerivativeTerm z hz n).val
      (pairedDivisionSecondDerivativeTerm a ha n).val) (61440*reciprocalSquare (n+1)*H) := by
  let r := reciprocalSquare (n+1)
  let i := (pairedSmallDiskLiteralInverseMap n).eval a ha
  let j := (pairedSmallDiskLiteralInverseMap n).eval z hz
  let da := pairedSmallDisk_domain a (1/4) (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ a ha)
  let dz := pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ z hz)
  have hp : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  have hr : 0≤r := Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp))
  have hr1 : r≤1 := by
    have h := reciprocalSquare_antitone 1 (n+1) (by omega) (by omega)
    simpa only [show reciprocalSquare 1=1 by decide +kernel] using h
  have hi : Small i.val (4*r) := pairedSmallDiskLiteralInverse_bound a (LocalODE.interior_bound _ a ha) n
  have hj : Small j.val (4*r) := pairedSmallDiskLiteralInverse_bound z (LocalODE.interior_bound _ z hz) n
  have hi4 : Small i.val 4 := hi.mono (by grind only)
  have hj4 : Small j.val 4 := hj.mono (by grind only)
  have hden := pairedLiteralDenominator_difference_bound a z (LocalODE.interior_bound _ a ha)
    (LocalODE.interior_bound _ z hz) (pairedIntegerSquare (n+1)) H hH hd
  have hdelta := pairedBoundaryReciprocal_difference_bound _ _ (dz n) (da n) H (4*r) 4
    hH (by grind only) (by decide +kernel) (RepresentedCauchySum.small_sub_symm _ _ _ hden) hj hi4
  have h64 : 0≤64*r*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hr) hH
  have hdi : Small (sub j.val i.val) (64*r*H) := hdelta.mono (by grind only)
  have hii := Small.mul i.property i.property (show (0:Rat)≤4 by decide) (show (0:Rat)≤4 by decide) hi4 hi4
  have hjj := Small.mul j.property j.property (show (0:Rat)≤4 by decide) (show (0:Rat)≤4 by decide) hj4 hj4
  have hsq := SeriesLimitLaws.product_close j.val j.val i.val i.val j.property j.property i.property i.property
    (64*r*H) (64*r*H) 4 4 h64 h64 (by decide +kernel) (by decide +kernel) hdi hdi hi4 hj4
  have h1024 : 0≤1024*r*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hr) hH
  have hsq' : Small (sub (mul j.val j.val) (mul i.val i.val)) (1024*r*H) := hsq.mono (by grind only)
  have hcu := SeriesLimitLaws.product_close j.val (mul j.val j.val) i.val (mul i.val i.val)
    j.property (mul_valid j.property j.property) i.property (mul_valid i.property i.property)
    (64*r*H) (1024*r*H) 4 (2*4*4) h64 h1024 (by decide +kernel) (by decide +kernel)
    hdi hsq' hi4 hjj
  have h12288 : 0≤12288*r*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hr) hH
  have hcu' : Small (sub (mul j.val (mul j.val j.val)) (mul i.val (mul i.val i.val)))
      (12288*r*H) := hcu.mono (by grind only)
  have hic := Small.mul j.property (mul_valid j.property j.property)
    (Rat.mul_nonneg (by decide +kernel) hr) (by decide +kernel) hj hjj
  have hzz := Small.mul a.property a.property (show (0:Rat)≤1/4 by decide +kernel)
    (show (0:Rat)≤1/4 by decide +kernel) (LocalODE.interior_bound _ a ha) (LocalODE.interior_bound _ a ha)
  have hzsq := SeriesLimitLaws.product_close z.val z.val a.val a.val
    z.property z.property a.property a.property H H (1/4) (1/4) hH hH
    (by decide +kernel) (by decide +kernel) hd hd
    (LocalODE.interior_bound _ a ha) (LocalODE.interior_bound _ z hz)
  have hzsq' : Small (sub (mul z.val z.val) (mul a.val a.val)) H := hzsq.mono (by grind only)
  have hb := SeriesLimitLaws.product_close (mul z.val z.val) (mul j.val (mul j.val j.val))
    (mul a.val a.val) (mul i.val (mul i.val i.val))
    (mul_valid z.property z.property) (mul_valid j.property (mul_valid j.property j.property))
    (mul_valid a.property a.property) (mul_valid i.property (mul_valid i.property i.property))
    H (12288*r*H) (2*(1/4)*(1/4)) (2*(4*r)*(2*4*4)) hH h12288
    (by decide +kernel) (by grind only) hzsq' hcu' hzz hic
  let az : Scalar := ⟨neg (mul j.val j.val),neg_valid (mul_valid j.property j.property)⟩
  let aa : Scalar := ⟨neg (mul i.val i.val),neg_valid (mul_valid i.property i.property)⟩
  have hneg : (neg (sub (mul j.val j.val) (mul i.val i.val))).Equiv (sub az.val aa.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (sub_valid (mul_valid j.property j.property) (mul_valid i.property i.property)))
      (hright := sub_valid az.property aa.property)
    let I := ComplexRawQuotient.ofRaw i.val i.property
    let J := ComplexRawQuotient.ofRaw j.val j.property
    change -(J*J-I*I)= -(J*J)- -(I*I)
    grind only
  have han := Small.congr
    (neg_valid (sub_valid (mul_valid j.property j.property) (mul_valid i.property i.property)))
    (sub_valid az.property aa.property) hneg (SeriesLimitLaws.small_neg hsq')
  let bz : Scalar := ⟨mul (mul z.val z.val) (mul j.val (mul j.val j.val)),
    mul_valid (mul_valid z.property z.property) (mul_valid j.property (mul_valid j.property j.property))⟩
  let ba : Scalar := ⟨mul (mul a.val a.val) (mul i.val (mul i.val i.val)),
    mul_valid (mul_valid a.property a.property) (mul_valid i.property (mul_valid i.property i.property))⟩
  have hb' : Small (sub bz.val ba.val) (3584*r*H) := hb.mono (by grind only)
  have hadd (x y u v : Scalar) (X Y : Rat) (hx : Small (sub x.val y.val) X)
      (hy : Small (sub u.val v.val) Y) :
      Small (sub (DomainFunctions.scalarSum x u).val (DomainFunctions.scalarSum y v).val) (X+Y) :=
    Small.congr (add_valid (sub_valid x.property y.property) (sub_valid u.property v.property))
      (sub_valid (DomainFunctions.scalarSum x u).property (DomainFunctions.scalarSum y v).property)
      (equiv_symm (DomainFunctions.scalarSum_difference x u y v)) (LocalODE.small_add hx hy)
  have ha2 := hadd az aa az aa _ _ han han
  have ha4 := hadd _ _ _ _ _ _ ha2 ha2
  have hb2 := hadd bz ba bz ba _ _ hb' hb'
  have hb4 := hadd _ _ _ _ _ _ hb2 hb2
  have hb8 := hadd _ _ _ _ _ _ hb4 hb4
  have hb16 := hadd _ _ _ _ _ _ hb8 hb8
  exact (hadd _ _ _ _ _ _ ha4 hb16).mono (by grind only)

end ComputableAnalysis.ModularForms
