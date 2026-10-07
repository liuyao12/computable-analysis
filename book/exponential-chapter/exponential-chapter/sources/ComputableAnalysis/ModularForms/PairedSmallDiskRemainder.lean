import ComputableAnalysis.ModularForms.PairedSmallDiskDerivative

/-! Quadratic, summable remainders on the full small disk, including zero. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem smallDiskShift_displacement (n : Nat) (plus : Bool) (a z : Scalar) :
    (sub (smallDiskShift z n plus).val (smallDiskShift a n plus).val).Equiv
      (sub z.val a.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (smallDiskShift z n plus).property (smallDiskShift a n plus).property)
    (hright := sub_valid z.property a.property)
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let C := ComplexRawQuotient.ofRaw (boundaryIntegerScalar (n+1)).val (boundaryIntegerScalar (n+1)).property
  cases plus with
  | false => change (Z-C)-(A-C)=Z-A; grind only
  | true => change (Z+C)-(A+C)=Z-A; grind only

theorem smallDiskShiftMap_remainder (n : Nat) (plus : Bool) (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z) :
    (DomainFunctions.remainder (smallDiskShiftMap n plus) a ha
      (ReciprocalDifference.derivative (smallDiskShift a n plus)
        (smallDiskShift_nonzero a (LocalODE.interior_bound _ a ha) n plus)) z hz).Equiv
      (mul (mul (mul ((smallDiskShiftMap n plus).eval a ha).val
        ((smallDiskShiftMap n plus).eval a ha).val)
        (mul (sub z.val a.val) (sub z.val a.val)))
        ((smallDiskShiftMap n plus).eval z hz).val) := by
  let A := smallDiskShift a n plus
  let Z := smallDiskShift z n plus
  let hA := smallDiskShift_nonzero a (LocalODE.interior_bound _ a ha) n plus
  let hZ := smallDiskShift_nonzero z (LocalODE.interior_bound _ z hz) n plus
  have he := smallDiskShift_displacement n plus a z
  have hR := ReciprocalDifference.remainder A Z hA hZ
  have hd := mul_equiv (ReciprocalDifference.derivative A hA).property
    (ReciprocalDifference.derivative A hA).property (sub_valid Z.property A.property)
    (sub_valid z.property a.property) (equiv_refl _ (ReciprocalDifference.derivative A hA).property) he
  have hl := FunctionTheory.sub_congr
    (equiv_refl _ (sub_valid (RepresentedReciprocal.inverse Z hZ).property
      (RepresentedReciprocal.inverse A hA).property)) hd
  have hsq := mul_equiv (sub_valid Z.property A.property) (sub_valid z.property a.property)
    (sub_valid Z.property A.property) (sub_valid z.property a.property) he he
  have hr := mul_equiv
    (mul_valid (mul_valid (RepresentedReciprocal.inverse A hA).property (RepresentedReciprocal.inverse A hA).property)
      (mul_valid (sub_valid Z.property A.property) (sub_valid Z.property A.property)))
    (mul_valid (mul_valid (RepresentedReciprocal.inverse A hA).property (RepresentedReciprocal.inverse A hA).property)
      (mul_valid (sub_valid z.property a.property) (sub_valid z.property a.property)))
    (RepresentedReciprocal.inverse Z hZ).property (RepresentedReciprocal.inverse Z hZ).property
    (mul_equiv (mul_valid (RepresentedReciprocal.inverse A hA).property (RepresentedReciprocal.inverse A hA).property)
      (mul_valid (RepresentedReciprocal.inverse A hA).property (RepresentedReciprocal.inverse A hA).property)
      (mul_valid (sub_valid Z.property A.property) (sub_valid Z.property A.property))
      (mul_valid (sub_valid z.property a.property) (sub_valid z.property a.property))
      (equiv_refl _ (mul_valid (RepresentedReciprocal.inverse A hA).property (RepresentedReciprocal.inverse A hA).property)) hsq)
    (equiv_refl _ (RepresentedReciprocal.inverse Z hZ).property)
  have vleft := sub_valid (sub_valid (RepresentedReciprocal.inverse Z hZ).property
    (RepresentedReciprocal.inverse A hA).property)
    (mul_valid (ReciprocalDifference.derivative A hA).property (sub_valid Z.property A.property))
  have vmid := mul_valid (mul_valid
    (mul_valid (RepresentedReciprocal.inverse A hA).property (RepresentedReciprocal.inverse A hA).property)
    (mul_valid (sub_valid Z.property A.property) (sub_valid Z.property A.property)))
    (RepresentedReciprocal.inverse Z hZ).property
  have vright := mul_valid (mul_valid
    (mul_valid (RepresentedReciprocal.inverse A hA).property (RepresentedReciprocal.inverse A hA).property)
    (mul_valid (sub_valid z.property a.property) (sub_valid z.property a.property)))
    (RepresentedReciprocal.inverse Z hZ).property
  exact equiv_trans (DomainFunctions.remainder_valid _ _ _ _ _ _) vleft vright
    (equiv_symm hl) (equiv_trans vleft vmid vright hR hr)

theorem smallDiskShiftMap_remainder_bound (n : Nat) (plus : Bool) (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (M H : Rat) (hM : 0≤M) (hH : 0≤H)
    (hA : Small ((smallDiskShiftMap n plus).eval a ha).val M)
    (hZ : Small ((smallDiskShiftMap n plus).eval z hz).val M)
    (hd : Small (sub z.val a.val) H) :
    Small (DomainFunctions.remainder (smallDiskShiftMap n plus) a ha
      (ReciprocalDifference.derivative (smallDiskShift a n plus)
        (smallDiskShift_nonzero a (LocalODE.interior_bound _ a ha) n plus)) z hz)
      (16*M*M*M*H*H) := by
  let I := (smallDiskShiftMap n plus).eval a ha
  let J := (smallDiskShiftMap n plus).eval z hz
  have hM2 := Rat.mul_nonneg (Rat.mul_nonneg (show (0:Rat)≤2 by decide) hM) hM
  have hH2 := Rat.mul_nonneg (Rat.mul_nonneg (show (0:Rat)≤2 by decide) hH) hH
  have hi := Small.mul I.property I.property hM hM hA hA
  have hh := Small.mul (sub_valid z.property a.property) (sub_valid z.property a.property) hH hH hd hd
  have hm := Small.mul (mul_valid I.property I.property)
    (mul_valid (sub_valid z.property a.property) (sub_valid z.property a.property)) hM2 hH2 hi hh
  have hmid := Rat.mul_nonneg (Rat.mul_nonneg (show (0:Rat)≤2 by decide) hM2) hH2
  have hb := (Small.mul (mul_valid (mul_valid I.property I.property)
    (mul_valid (sub_valid z.property a.property) (sub_valid z.property a.property))) J.property hmid hM hm hZ).mono
    (show (2:Rat)*(2*(2*M*M)*(2*H*H))*M≤16*M*M*M*H*H by grind only)
  exact Small.congr (mul_valid (mul_valid (mul_valid I.property I.property)
    (mul_valid (sub_valid z.property a.property) (sub_valid z.property a.property))) J.property)
    (DomainFunctions.remainder_valid _ _ _ _ _ _)
    (equiv_symm (smallDiskShiftMap_remainder n plus a z ha hz)) hb

theorem pairedSmallDiskTermMap_remainder_uniform (n : Nat) (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (M H : Rat) (hM : 0≤M) (hH : 0≤H)
    (hAm : Small ((smallDiskShiftMap n false).eval a ha).val M)
    (hAp : Small ((smallDiskShiftMap n true).eval a ha).val M)
    (hZm : Small ((smallDiskShiftMap n false).eval z hz).val M)
    (hZp : Small ((smallDiskShiftMap n true).eval z hz).val M)
    (hd : Small (sub z.val a.val) H) :
    Small (DomainFunctions.remainder (pairedSmallDiskTermMap n) a ha
      (pairedSmallDiskDerivativeTerm a (LocalODE.interior_bound _ a ha) n) z hz)
      (32*M*M*M*H*H) := by
  let dm := ReciprocalDifference.derivative (smallDiskShift a n false)
    (smallDiskShift_nonzero a (LocalODE.interior_bound _ a ha) n false)
  let dp := ReciprocalDifference.derivative (smallDiskShift a n true)
    (smallDiskShift_nonzero a (LocalODE.interior_bound _ a ha) n true)
  have hm := smallDiskShiftMap_remainder_bound n false a z ha hz M H hM hH hAm hZm hd
  have hp := smallDiskShiftMap_remainder_bound n true a z ha hz M H hM hH hAp hZp hd
  have hb := (LocalODE.small_add hm hp).mono
    (show (16:Rat)*M*M*M*H*H+16*M*M*M*H*H≤32*M*M*M*H*H by grind only)
  exact Small.congr
    (add_valid (DomainFunctions.remainder_valid (smallDiskShiftMap n false) a ha dm z hz)
      (DomainFunctions.remainder_valid (smallDiskShiftMap n true) a ha dp z hz))
    (DomainFunctions.remainder_valid (pairedSmallDiskTermMap n) a ha
      (pairedSmallDiskDerivativeTerm a (LocalODE.interior_bound _ a ha) n) z hz)
    (equiv_symm (sum_remainder (smallDiskShiftMap n false) (smallDiskShiftMap n true)
      (fun (w : Scalar) (hw : LocalODE.interior (1/4) w) => hw) a ha dm dp z hz)) hb

theorem pairedSmallDiskTermMap_remainder_bound (n : Nat) (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (DomainFunctions.remainder (pairedSmallDiskTermMap n) a ha
      (pairedSmallDiskDerivativeTerm a (LocalODE.interior_bound _ a ha) n) z hz)
      (131072*reciprocalSquare (n+1)*H*H) := by
  have hn : 0<n+1 := by omega
  have hp : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast hn
  have hi0 : 0≤(((n+1:Nat):Rat))⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hp)
  have hM : 0≤16*(1/((n+1:Nat):Rat)) := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.mul_nonneg (by decide) hi0
  have h := pairedSmallDiskTermMap_remainder_uniform n a z ha hz
    (16*(1/((n+1:Nat):Rat))) H hM hH
    (smallDiskShiftInverse_bound a (LocalODE.interior_bound _ a ha) n false)
    (smallDiskShiftInverse_bound a (LocalODE.interior_bound _ a ha) n true)
    (smallDiskShiftInverse_bound z (LocalODE.interior_bound _ z hz) n false)
    (smallDiskShiftInverse_bound z (LocalODE.interior_bound _ z hz) n true) hd
  apply h.mono
  have he := Rat.mul_inv_cancel (((n+1:Nat):Rat)) (Rat.ne_of_gt hp)
  have hn1 : (1:Rat)≤((n+1:Nat):Rat) := by exact_mod_cast (show 1≤n+1 by omega)
  have hi1 : (((n+1:Nat):Rat))⁻¹≤1 := by
    have hm := Rat.mul_le_mul_of_nonneg_right hn1 hi0
    rw [Rat.one_mul,he] at hm
    exact hm
  let i := (((n+1:Nat):Rat))⁻¹
  have his : 0≤i*i := Rat.mul_nonneg hi0 hi0
  have hic : i*i*i≤i*i := by
    have hm := Rat.mul_le_mul_of_nonneg_left hi1 his
    simpa only [Rat.mul_one] using hm
  have hC : 0≤(131072:Rat)*H*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) hH
  calc
    _ = (131072*H*H)*(i*i*i) := by dsimp [i]; rw [Rat.div_def,Rat.one_mul]; grind only
    _ ≤ (131072*H*H)*(i*i) := Rat.mul_le_mul_of_nonneg_left hic hC
    _ = _ := by rw [pairedDerivative_reciprocalSquare_eq_inverse_product (n+1) hn]; dsimp [i]; grind only

theorem pairedSmallDiskRemainder_block_bound (N k : Nat) (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (ScalarSeries.block (fun n => DomainFunctions.remainder (pairedSmallDiskTermMap n) a ha
      (pairedSmallDiskDerivativeTerm a (LocalODE.interior_bound _ a ha) n) z hz) N k)
      (131072*reciprocalSquareBlock N k*H*H) := by
  induction k with
  | zero => exact Small.zero (by simp only [reciprocalSquareBlock,Rat.mul_zero,Rat.zero_mul]; decide +kernel)
  | succ k ih =>
    have h := LocalODE.small_add ih (pairedSmallDiskTermMap_remainder_bound (N+k) a z ha hz H hH hd)
    apply h.mono
    change 131072*reciprocalSquareBlock N k*H*H +
      131072*reciprocalSquare (N+k+1)*H*H≤131072*reciprocalSquareBlock N (k+1)*H*H
    rw [reciprocalSquareBlock]
    grind only

theorem pairedSmallDiskRemainder_block_tail (N k : Nat) (hN : 0<N) (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (ScalarSeries.block (fun n => DomainFunctions.remainder (pairedSmallDiskTermMap n) a ha
      (pairedSmallDiskDerivativeTerm a (LocalODE.interior_bound _ a ha) n) z hz) N k)
      (131072*(N:Rat)⁻¹*H*H) := by
  apply (pairedSmallDiskRemainder_block_bound N k a z ha hz H hH hd).mono
  have hC : 0≤(131072:Rat)*H*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) hH
  have hm := Rat.mul_le_mul_of_nonneg_left (reciprocalSquareBlock_tail N k hN) hC
  grind only

private theorem smallDiskRemainder_squareBlock_split (k : Nat) :
    reciprocalSquareBlock 0 (k+1)=1+reciprocalSquareBlock 1 k := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    change reciprocalSquareBlock 0 (k+1)+reciprocalSquare (0+(k+1)+1)=
      1+(reciprocalSquareBlock 1 k+reciprocalSquare (1+k+1))
    rw [ih,show 0+(k+1)+1=1+k+1 by omega]
    grind only

private theorem smallDiskRemainder_squareBlock_zero_bound (k : Nat) :
    reciprocalSquareBlock 0 k≤2 := by
  cases k with
  | zero => change (0:Rat)≤2; decide +kernel
  | succ k =>
    rw [smallDiskRemainder_squareBlock_split]
    have h := reciprocalSquareBlock_tail 1 k (by omega)
    have he : ((1:Nat):Rat)⁻¹=1 := by decide +kernel
    rw [he] at h
    grind only

theorem pairedSmallDiskRemainder_prefix_bound (k : Nat) (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (ScalarSeries.block (fun n => DomainFunctions.remainder (pairedSmallDiskTermMap n) a ha
      (pairedSmallDiskDerivativeTerm a (LocalODE.interior_bound _ a ha) n) z hz) 0 k)
      (262144*H*H) := by
  apply (pairedSmallDiskRemainder_block_bound 0 k a z ha hz H hH hd).mono
  have hC : 0≤(131072:Rat)*H*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) hH
  have hm := Rat.mul_le_mul_of_nonneg_left (smallDiskRemainder_squareBlock_zero_bound k) hC
  grind only

end ComputableAnalysis.ModularForms
