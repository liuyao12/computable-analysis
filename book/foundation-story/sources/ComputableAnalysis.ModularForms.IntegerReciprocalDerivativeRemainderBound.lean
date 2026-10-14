import ComputableAnalysis.ModularForms.IntegerReciprocalDerivativeRemainder
import ComputableAnalysis.ModularForms.LatticeReciprocalDifference

/-! Quantitative quadratic remainders for the global derivative terms. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem integerReciprocalDerivativeRemainder_bound (k : Int) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (H M : Rat) (hH : 0≤H) (hM : 0≤M) (hd : Small (sub z.val a.val) H)
    (hi : Small ((integerReciprocalMap k).eval a ha).val M)
    (hj : Small ((integerReciprocalMap k).eval z hz).val M) :
    Small (integerReciprocalDerivativeRemainder k a z ha hz).val (96*M*M*M*M*H*H) := by
  let i := (integerReciprocalMap k).eval a ha
  let j := (integerReciprocalMap k).eval z hz
  have hshift : (sub z.val a.val).Equiv
      (sub (integerShiftScalar z k).val (integerShiftScalar a k).val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid z.property a.property)
      (hright := sub_valid (integerShiftScalar z k).property (integerShiftScalar a k).property)
    change ComplexRawQuotient.ofRaw z.val z.property-ComplexRawQuotient.ofRaw a.val a.property =
      ComplexRawQuotient.ofRaw (integerAffine 1 k z.val) (integerShiftScalar z k).property-
      ComplexRawQuotient.ofRaw (integerAffine 1 k a.val) (integerShiftScalar a k).property
    rw [integerAffine_class,integerAffine_class]
    grind only
  have hs := Small.congr (sub_valid z.property a.property)
    (sub_valid (integerShiftScalar z k).property (integerShiftScalar a k).property) hshift hd
  have hdelta := pairedBoundaryReciprocal_difference_bound
    (integerShiftScalar z k) (integerShiftScalar a k)
    (upperScalar_nonzero _ (integerShiftScalar_upper z hz k))
    (upperScalar_nonzero _ (integerShiftScalar_upper a ha k)) H M M hH hM hM
    (RepresentedCauchySum.small_sub_symm _ _ _ hs) hj hi
  have hsq := Small.mul i.property i.property hM hM hi hi
  have hn2 : 0≤2*M*M := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hM
  have hcu := Small.mul (mul_valid i.property i.property) j.property hn2 hM hsq hj
  have hn3 : 0≤2*(2*M*M)*M := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hn2) hM
  have hh := Small.mul (sub_valid z.property a.property) (sub_valid z.property a.property) hH hH hd hd
  have hhh : 0≤2*H*H := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) hH
  have hr := Small.mul (mul_valid (mul_valid i.property i.property) j.property)
    (mul_valid (sub_valid z.property a.property) (sub_valid z.property a.property)) hn3 hhh hcu hh
  have hnr : 0≤2*(2*(2*M*M)*M)*(2*H*H) := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hn3) hhh
  have hir := Small.mul i.property
    (mul_valid (mul_valid (mul_valid i.property i.property) j.property)
      (mul_valid (sub_valid z.property a.property) (sub_valid z.property a.property))) hM hnr hi hr
  have hnd : 0≤4*H*M*M := Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) hM) hM
  have hdd := Small.mul (sub_valid j.property i.property) (sub_valid j.property i.property)
    hnd hnd hdelta hdelta
  exact (SeriesLimitLaws.small_neg (LocalODE.small_add (LocalODE.small_add hir hir) hdd)).mono (by grind only)

end ComputableAnalysis.ModularForms
