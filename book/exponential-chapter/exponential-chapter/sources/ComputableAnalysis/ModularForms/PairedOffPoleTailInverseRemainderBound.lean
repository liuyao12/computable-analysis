import ComputableAnalysis.ModularForms.PairedOffPoleTailInverseQuadratic

/-! Quantitative quadratic bounds for the actual off-pole inverse remainder. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedOffPole_squared_difference_bound (B : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (sub (mul z.val z.val) (mul a.val a.val)) (4*(B:Rat)*H) := by
  have hs := LocalODE.small_add (LocalODE.interior_bound _ z hz) (LocalODE.interior_bound _ a ha)
  have hp := Small.mul (add_valid z.property a.property) (sub_valid z.property a.property)
    (Rat.add_nonneg Rat.natCast_nonneg Rat.natCast_nonneg) hH hs hd
  have he : (mul (add z.val a.val) (sub z.val a.val)).Equiv
      (sub (mul z.val z.val) (mul a.val a.val)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid (add_valid z.property a.property) (sub_valid z.property a.property))
      (hright := sub_valid (mul_valid z.property z.property) (mul_valid a.property a.property))
    let A := ComplexRawQuotient.ofRaw a.val a.property
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change (Z+A)*(Z-A)=Z*Z-A*A
    grind only
  exact (Small.congr (mul_valid (add_valid z.property a.property) (sub_valid z.property a.property))
    (sub_valid (mul_valid z.property z.property) (mul_valid a.property a.property)) he hp).mono (by grind only)

theorem pairedOffPoleTailInverseRemainder_bound_of_reciprocals (B n : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z)
    (M H : Rat) (hM : 0≤M) (hH : 0≤H)
    (hi : Small (pairedOffPoleTailInverse B n a ha).val M)
    (hj : Small (pairedOffPoleTailInverse B n z hz).val M)
    (hd : Small (sub z.val a.val) H) :
    Small (pairedOffPoleTailInverseRemainder B n a z ha hz).val
      ((256*(B:Rat)*(B:Rat)*M*M*M+8*M*M)*H*H) := by
  let i := pairedOffPoleTailInverse B n a ha
  let j := pairedOffPoleTailInverse B n z hz
  let d : Scalar := ⟨sub (mul z.val z.val) (mul a.val a.val),
    sub_valid (mul_valid z.property z.property) (mul_valid a.property a.property)⟩
  let h : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
  have hD := pairedOffPole_squared_difference_bound B a z ha hz H hH hd
  have hDb : 0≤4*(B:Rat)*H := Rat.mul_nonneg
    (Rat.mul_nonneg (by decide +kernel) Rat.natCast_nonneg) hH
  have hii := Small.mul i.property i.property hM hM hi hi
  have hdd := Small.mul d.property d.property hDb hDb hD hD
  have hhh := Small.mul h.property h.property hH hH hd hd
  have hI2 : 0≤2*M*M := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hM) hM
  have hD2 : 0≤2*(4*(B:Rat)*H)*(4*(B:Rat)*H) :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hDb) hDb
  have hH2 : 0≤2*H*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hH) hH
  have hid := Small.mul (mul_valid i.property i.property) (mul_valid d.property d.property)
    hI2 hD2 hii hdd
  have hID : 0≤2*(2*M*M)*(2*(4*(B:Rat)*H)*(4*(B:Rat)*H)) :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hI2) hD2
  have hleft := Small.mul (mul_valid (mul_valid i.property i.property) (mul_valid d.property d.property))
    j.property hID hM hid hj
  have hright := Small.mul (mul_valid i.property i.property) (mul_valid h.property h.property)
    hI2 hH2 hii hhh
  have hb := SeriesLimitLaws.small_sub hleft hright
  have hquad : Small (pairedOffPoleTailInverseQuadratic B n a z ha hz).val
      ((256*(B:Rat)*(B:Rat)*M*M*M+8*M*M)*H*H) := hb.mono (by grind only)
  exact Small.congr (pairedOffPoleTailInverseQuadratic B n a z ha hz).property
    (pairedOffPoleTailInverseRemainder B n a z ha hz).property
    (equiv_symm (pairedOffPoleTailInverse_remainder_quadratic B n a z ha hz)) hquad


theorem pairedOffPoleTailInverseRemainder_square_bound (B n : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (pairedOffPoleTailInverseRemainder B n a z ha hz).val
      ((128+16384*(B:Rat)*(B:Rat))*reciprocalSquare (n+1)*H*H) := by
  let r := reciprocalSquare (pairedTailShift B n)
  have hr : 0≤r := by
    unfold r reciprocalSquare
    exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos
      (by exact_mod_cast (show 0<pairedTailShift B n by unfold pairedTailShift; omega))
      (by exact_mod_cast (show 0<pairedTailShift B n by unfold pairedTailShift; omega))))
  have hr1 := pairedDerivative_reciprocalSquare_antitone 1 (pairedTailShift B n)
    (by omega) (by unfold pairedTailShift; omega)
  rw [show reciprocalSquare 1=1 by decide +kernel] at hr1
  have hs := pairedDerivative_reciprocalSquare_antitone (n+1) (pairedTailShift B n)
    (by omega) (by unfold pairedTailShift; omega)
  have hrr : r*r≤r := by
    have h := Rat.mul_le_mul_of_nonneg_left hr1 hr
    grind only
  have hrrr : r*r*r≤r := by
    have h := Rat.mul_le_mul_of_nonneg_right hrr hr
    exact Rat.le_trans h hrr
  have hbb : 0≤16384*(B:Rat)*(B:Rat) := Rat.mul_nonneg
    (Rat.mul_nonneg (by decide +kernel) Rat.natCast_nonneg) Rat.natCast_nonneg
  have h3 := Rat.mul_le_mul_of_nonneg_left hrrr hbb
  have h2 := Rat.mul_le_mul_of_nonneg_left hrr (show (0:Rat)≤128 by decide +kernel)
  have hmajor := Rat.mul_le_mul_of_nonneg_left hs (show 0≤128+16384*(B:Rat)*(B:Rat) by grind only)
  have hc : (256*(B:Rat)*(B:Rat)*(4*r)*(4*r)*(4*r)+8*(4*r)*(4*r))≤
      (128+16384*(B:Rat)*(B:Rat))*reciprocalSquare (n+1) := by
    dsimp only [r] at h3 h2
    grind only
  have hb := pairedOffPoleTailInverseRemainder_bound_of_reciprocals B n a z ha hz (4*r) H
    (Rat.mul_nonneg (by decide +kernel) hr) hH
    (pairedOffPoleTailInverse_bound B n a ha) (pairedOffPoleTailInverse_bound B n z hz) hd
  exact hb.mono (Rat.mul_le_mul_of_nonneg_right
    (Rat.mul_le_mul_of_nonneg_right hc hH) hH)

end ComputableAnalysis.ModularForms
