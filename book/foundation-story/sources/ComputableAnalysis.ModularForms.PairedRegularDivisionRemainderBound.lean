import ComputableAnalysis.ModularForms.PairedRegularDivisionRemainder

/-! Summable quadratic bounds for regular-division remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedRegularDivisionRemainder_bound (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (n : Nat) :
    Small (pairedRegularDivisionRemainder a z ha hz n).val
      (2304*reciprocalSquare (n+1)*H*H) := by
  let r := reciprocalSquare (n+1)
  let M := 4*r
  let i := (pairedSmallDiskLiteralInverseMap n).eval a ha
  let j := (pairedSmallDiskLiteralInverseMap n).eval z hz
  let d : Scalar := ⟨sub (mul z.val z.val) (mul a.val a.val),
    sub_valid (mul_valid z.property z.property) (mul_valid a.property a.property)⟩
  let h : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
  have hp : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  have hr : 0≤r := by
    dsimp [r]; unfold reciprocalSquare
    exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp))
  have hm : 0≤M := Rat.mul_nonneg (by decide) hr
  have hi : Small i.val M := pairedSmallDiskLiteralInverse_bound a (LocalODE.interior_bound _ a ha) n
  have hj : Small j.val M := pairedSmallDiskLiteralInverse_bound z (LocalODE.interior_bound _ z hz) n
  have hden : Small d.val H := by
    have hs := LocalODE.small_add (LocalODE.interior_bound _ z hz) (LocalODE.interior_bound _ a ha)
    have hb := Small.mul h.property (add_valid z.property a.property) hH
      (show (0:Rat)≤1/4+1/4 by decide +kernel) hd hs
    have he : (mul h.val (add z.val a.val)).Equiv d.val := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := mul_valid h.property (add_valid z.property a.property)) (hright := d.property)
      let A := ComplexRawQuotient.ofRaw a.val a.property
      let Z := ComplexRawQuotient.ofRaw z.val z.property
      change (Z-A)*(Z+A)=Z*Z-A*A
      grind only
    rw [show (2:Rat)*H*(1/4+1/4)=H by grind only] at hb
    exact Small.congr (mul_valid h.property (add_valid z.property a.property)) d.property he hb
  have hH2 : 0≤2*H*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) hH
  have hi2 := Small.mul i.property i.property hm hm hi hi
  have hd2 := Small.mul d.property d.property hH hH hden hden
  have hh2 := Small.mul h.property h.property hH hH hd hd
  have hdj := Small.mul (mul_valid d.property d.property) j.property hH2 hm hd2 hj
  have hsub := SeriesLimitLaws.small_sub hdj hh2
  have hs := Small.mul (mul_valid i.property i.property)
    (sub_valid (mul_valid (mul_valid d.property d.property) j.property) (mul_valid h.property h.property))
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hm) hm)
    (Rat.add_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH2) hm) hH2) hi2 hsub
  have hb := LocalODE.small_add hs hs
  apply hb.mono
  have hr1 := reciprocalSquare_antitone 1 (n+1) (by omega) (by omega)
  rw [show reciprocalSquare 1=1 by decide +kernel] at hr1
  have hrsq := Rat.mul_le_mul_of_nonneg_left hr1 hr
  have hrcube := Rat.mul_le_mul_of_nonneg_left hr1 (Rat.mul_nonneg hr hr)
  have hsH := Rat.mul_le_mul_of_nonneg_right hrsq (Rat.mul_nonneg hH hH)
  have hcH := Rat.mul_le_mul_of_nonneg_right hrcube (Rat.mul_nonneg hH hH)
  dsimp [M,r] at *
  grind only

end ComputableAnalysis.ModularForms
