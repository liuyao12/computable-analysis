import ComputableAnalysis.ModularForms.PairedDerivativeInvariance
import ComputableAnalysis.ModularForms.LatticeReciprocalDifference

/-! Uniform first differences of actual paired reciprocal derivatives. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedUniformReciprocalDerivative_difference (a z : Scalar)
    (ha : NonzeroBoxSearch.Nonzero a) (hz : NonzeroBoxSearch.Nonzero z)
    (M H : Rat) (hM : 0≤M) (hH : 0≤H)
    (hIa : Small (RepresentedReciprocal.inverse a ha).val M)
    (hIz : Small (RepresentedReciprocal.inverse z hz).val M)
    (hd : Small (sub z.val a.val) H) :
    Small (sub (ReciprocalDifference.derivative z hz).val
      (ReciprocalDifference.derivative a ha).val) (16*M*M*M*H) := by
  have hi := pairedBoundaryReciprocal_difference_bound z a hz ha H M M hH hM hM
    (RepresentedCauchySum.small_sub_symm _ _ _ hd) hIz hIa
  have hs := LocalODE.small_add hIz hIa
  have hb := SeriesLimitLaws.small_neg (Small.mul
    (add_valid (RepresentedReciprocal.inverse z hz).property (RepresentedReciprocal.inverse a ha).property)
    (sub_valid (RepresentedReciprocal.inverse z hz).property (RepresentedReciprocal.inverse a ha).property)
    (Rat.add_nonneg hM hM)
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) hM) hM) hs hi)
  have he : (2:Rat)*(M+M)*(4*H*M*M)=16*M*M*M*H := by grind only
  rw [he] at hb
  exact Small.congr
    (neg_valid (mul_valid
      (add_valid (RepresentedReciprocal.inverse z hz).property (RepresentedReciprocal.inverse a ha).property)
      (sub_valid (RepresentedReciprocal.inverse z hz).property (RepresentedReciprocal.inverse a ha).property)))
    (sub_valid (ReciprocalDifference.derivative z hz).property (ReciprocalDifference.derivative a ha).property)
    (equiv_symm (ReciprocalDifference.derivative_difference a z ha hz)) hb

private theorem pairedMinus_displacement (a z c : Scalar) :
    (sub (pairedMinus z c).val (pairedMinus a c).val).Equiv (sub z.val a.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (pairedMinus z c).property (pairedMinus a c).property)
    (hright := sub_valid z.property a.property)
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let C := ComplexRawQuotient.ofRaw c.val c.property
  change (Z-C)-(A-C)=Z-A
  grind only

private theorem pairedPlus_displacement (a z c : Scalar) :
    (sub (pairedPlus z c).val (pairedPlus a c).val).Equiv (sub z.val a.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (pairedPlus z c).property (pairedPlus a c).property)
    (hright := sub_valid z.property a.property)
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let C := ComplexRawQuotient.ofRaw c.val c.property
  change (Z+C)-(A+C)=Z-A
  grind only

theorem upperPairedReciprocalDerivative_difference_uniform (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) (n : Nat)
    (M H : Rat) (hM : 0≤M) (hH : 0≤H)
    (hAm : Small (RepresentedReciprocal.inverse (pairedMinus a (boundaryIntegerScalar n))
      (upperShiftMinus_nonzero a ha (n:Rat))).val M)
    (hAp : Small (RepresentedReciprocal.inverse (pairedPlus a (boundaryIntegerScalar n))
      (upperShiftPlus_nonzero a ha (n:Rat))).val M)
    (hZm : Small (RepresentedReciprocal.inverse (pairedMinus z (boundaryIntegerScalar n))
      (upperShiftMinus_nonzero z hz (n:Rat))).val M)
    (hZp : Small (RepresentedReciprocal.inverse (pairedPlus z (boundaryIntegerScalar n))
      (upperShiftPlus_nonzero z hz (n:Rat))).val M)
    (hd : Small (sub z.val a.val) H) :
    Small (sub (upperPairedReciprocalDerivative z hz n).val
      (upperPairedReciprocalDerivative a ha n).val) (32*M*M*M*H) := by
  let c := boundaryIntegerScalar n
  have hmD := Small.congr (sub_valid z.property a.property)
    (sub_valid (pairedMinus z c).property (pairedMinus a c).property)
    (equiv_symm (pairedMinus_displacement a z c)) hd
  have hpD := Small.congr (sub_valid z.property a.property)
    (sub_valid (pairedPlus z c).property (pairedPlus a c).property)
    (equiv_symm (pairedPlus_displacement a z c)) hd
  have hm := pairedUniformReciprocalDerivative_difference (pairedMinus a c) (pairedMinus z c)
    (upperShiftMinus_nonzero a ha (n:Rat)) (upperShiftMinus_nonzero z hz (n:Rat)) M H hM hH hAm hZm hmD
  have hp := pairedUniformReciprocalDerivative_difference (pairedPlus a c) (pairedPlus z c)
    (upperShiftPlus_nonzero a ha (n:Rat)) (upperShiftPlus_nonzero z hz (n:Rat)) M H hM hH hAp hZp hpD
  have he := SeriesLimitLaws.addition_difference
    (ReciprocalDifference.derivative (pairedMinus z c) (upperShiftMinus_nonzero z hz (n:Rat))).val
    (ReciprocalDifference.derivative (pairedMinus a c) (upperShiftMinus_nonzero a ha (n:Rat))).val
    (ReciprocalDifference.derivative (pairedPlus z c) (upperShiftPlus_nonzero z hz (n:Rat))).val
    (ReciprocalDifference.derivative (pairedPlus a c) (upperShiftPlus_nonzero a ha (n:Rat))).val
    (ReciprocalDifference.derivative _ _).property (ReciprocalDifference.derivative _ _).property
    (ReciprocalDifference.derivative _ _).property (ReciprocalDifference.derivative _ _).property
  have h := (LocalODE.small_add hm hp).mono
    (show (16:Rat)*M*M*M*H+16*M*M*M*H≤32*M*M*M*H by grind only)
  exact Small.congr (add_valid (sub_valid (ReciprocalDifference.derivative _ _).property
      (ReciprocalDifference.derivative _ _).property)
      (sub_valid (ReciprocalDifference.derivative _ _).property (ReciprocalDifference.derivative _ _).property))
    (sub_valid (upperPairedReciprocalDerivative z hz n).property (upperPairedReciprocalDerivative a ha n).property)
    (equiv_symm he) h

theorem pairedDerivative_inverseCube_le_square (n : Nat) (hn : 0<n) :
    (n:Rat)⁻¹*(n:Rat)⁻¹*(n:Rat)⁻¹≤reciprocalSquare n := by
  have hp : (0:Rat)<(n:Rat) := by exact_mod_cast hn
  have hi0 : 0≤(n:Rat)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hp)
  have hi := Rat.mul_inv_cancel (n:Rat) (Rat.ne_of_gt hp)
  have hn1 : (1:Rat)≤(n:Rat) := by exact_mod_cast (show 1≤n by omega)
  have hm := Rat.mul_le_mul_of_nonneg_right hn1 hi0
  rw [Rat.one_mul,hi] at hm
  have hs := Rat.mul_le_mul_of_nonneg_left hm (Rat.mul_nonneg hi0 hi0)
  rw [Rat.mul_one] at hs
  rw [pairedDerivative_reciprocalSquare_eq_inverse_product n hn]
  exact hs

theorem upperPairedReciprocalDerivative_difference_large (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (R H : Rat) (hR : 0≤R) (hH : 0≤H) (hA : Small a.val R) (hZ : Small z.val R)
    (n : Nat) (hn : 0<n) (hlarge : 16*R*R≤pairedIntegerSquare n) (hRn : R≤(n:Rat))
    (hd : Small (sub z.val a.val) H) :
    Small (sub (upperPairedReciprocalDerivative z hz n).val
      (upperPairedReciprocalDerivative a ha n).val) (131072*reciprocalSquare n*H) := by
  have hp : (0:Rat)<(n:Rat) := by exact_mod_cast hn
  have hM : 0≤16*(1/(n:Rat)) := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.mul_nonneg (by decide) (Rat.le_of_lt (Rat.inv_pos.mpr hp))
  have h := upperPairedReciprocalDerivative_difference_uniform a z ha hz n
    (16*(1/(n:Rat))) H hM hH
    ((integerBoundaryMinus_bound a ha R hR hA n hn hlarge).mono (integerBoundaryRate_le R n hn hRn))
    ((integerBoundaryPlus_bound a ha R hR hA n hn hlarge).mono (integerBoundaryRate_le R n hn hRn))
    ((integerBoundaryMinus_bound z hz R hR hZ n hn hlarge).mono (integerBoundaryRate_le R n hn hRn))
    ((integerBoundaryPlus_bound z hz R hR hZ n hn hlarge).mono (integerBoundaryRate_le R n hn hRn)) hd
  apply h.mono
  have hc : 0≤(131072:Rat)*H := Rat.mul_nonneg (by decide) hH
  calc
    _ = (131072*H)*((n:Rat)⁻¹*(n:Rat)⁻¹*(n:Rat)⁻¹) := by rw [Rat.div_def,Rat.one_mul]; grind only
    _ ≤ (131072*H)*reciprocalSquare n :=
      Rat.mul_le_mul_of_nonneg_left (pairedDerivative_inverseCube_le_square n hn) hc
    _ = _ := by grind only

theorem pairedDerivativeTailTerm_difference_bound (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (n : Nat) :
    Small (sub (pairedDerivativeTailTerm z hz B n).val (pairedDerivativeTailTerm a ha B n).val)
      (131072*reciprocalSquare (n+1)*H) := by
  have hk : 0<pairedTailShift B n := by unfold pairedTailShift; omega
  have hRn : (B:Rat)≤((pairedTailShift B n):Rat) := by
    exact_mod_cast (show B≤pairedTailShift B n by unfold pairedTailShift; omega)
  have h := upperPairedReciprocalDerivative_difference_large a z ha hz (B:Rat) H
    Rat.natCast_nonneg hH hA hZ (pairedTailShift B n) hk (pairedTailShift_large B n) hRn hd
  apply h.mono
  have hs := pairedDerivative_reciprocalSquare_antitone (n+1) (pairedTailShift B n)
    (by omega) (by unfold pairedTailShift; omega)
  have hc := Rat.mul_le_mul_of_nonneg_left hs (Rat.mul_nonneg (show (0:Rat)≤131072 by decide) hH)
  change 131072*reciprocalSquare (pairedTailShift B n)*H≤_
  grind only

end ComputableAnalysis.ModularForms
