import ComputableAnalysis.ModularForms.PairedDivisionDerivativeRemainder

/-! Summable quadratic estimates for the actual derivative-term remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedDivisionDerivativeRemainder_bound (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (n : Nat) :
    Small (pairedDivisionDerivativeRemainder a z ha hz n).val
      (61440*reciprocalSquare (n+1)*H*H) := by
  let r := reciprocalSquare (n+1)
  let i := (pairedSmallDiskLiteralInverseMap n).eval a ha
  let j := (pairedSmallDiskLiteralInverseMap n).eval z hz
  let da := pairedSmallDisk_domain a (1/4) (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ a ha)
  let dz := pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ z hz)
  have hp : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  have hr : 0≤r := Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp))
  have hr1 : r≤1 := by
    have h := reciprocalSquare_antitone 1 (n+1) (by omega) (by omega)
    simpa only [show reciprocalSquare 1=1 by decide +kernel] using h
  have hi : Small i.val (4*r) := pairedSmallDiskLiteralInverse_bound a (LocalODE.interior_bound _ a ha) n
  have hj : Small j.val (4*r) := pairedSmallDiskLiteralInverse_bound z (LocalODE.interior_bound _ z hz) n
  have hi4 : Small i.val 4 := hi.mono (by grind only)
  have hj4 : Small j.val 4 := hj.mono (by grind only)
  have hdelta := pairedBoundaryReciprocal_difference_bound
    (pairedLiteralDenominator z (pairedIntegerSquare (n+1)))
    (pairedLiteralDenominator a (pairedIntegerSquare (n+1))) (dz n) (da n)
    H (4*r) 4 hH (by grind only) (by decide) 
    (RepresentedCauchySum.small_sub_symm _ _ _
      (pairedLiteralDenominator_difference_bound a z (LocalODE.interior_bound _ a ha)
        (LocalODE.interior_bound _ z hz) _ H hH hd)) hj hi4
  have hd64 : Small (sub j.val i.val) (64*r*H) := hdelta.mono (by grind only)
  have hdconst : Small (sub j.val i.val) (64*H) := hd64.mono (by
    have h := Rat.mul_le_mul_of_nonneg_right hr1 hH
    grind only)
  have h64 : 0≤64*r*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hr) hH
  have h64H : 0≤64*H := Rat.mul_nonneg (by decide) hH
  have h2304 : 0≤2304*reciprocalSquare (n+1)*H*H :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hr) hH) hH
  have hdsq :=  Small.mul (sub_valid j.property i.property) (sub_valid j.property i.property)
    h64 h64H hd64 hdconst
  have hq := SeriesLimitLaws.product_close j.val j.val i.val i.val
    j.property j.property i.property i.property
    (64*r*H) (64*r*H) 4 4 h64 h64
    (by decide) (by decide) hd64 hd64 hi4 hj4
  have hrem := pairedRegularDivisionRemainder_bound a z ha hz H hH hd n
  have hir := Small.mul i.property (pairedRegularDivisionRemainder a z ha hz n).property
    (show (0:Rat)≤4 by decide) h2304 hi4 hrem
  have hleft := Small.mul a.property
    (add_valid (mul_valid i.property (pairedRegularDivisionRemainder a z ha hz n).property)
      (mul_valid (sub_valid j.property i.property) (sub_valid j.property i.property)))
    (show (0:Rat)≤1/4 by decide +kernel) (by grind only)
    (LocalODE.interior_bound _ a ha) (LocalODE.small_add hir hdsq)
  have hright := Small.mul (sub_valid z.property a.property)
    (sub_valid (mul_valid j.property j.property) (mul_valid i.property i.property))
    hH (by grind only) hd hq
  have hv := SeriesLimitLaws.small_neg (LocalODE.small_add hleft hright)
  have hv2 := LocalODE.small_add hv hv
  exact (LocalODE.small_add hv2 hv2).mono (by grind only)

end ComputableAnalysis.ModularForms
