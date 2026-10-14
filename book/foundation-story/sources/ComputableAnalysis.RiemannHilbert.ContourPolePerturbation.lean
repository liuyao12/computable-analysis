import ComputableAnalysis.RiemannHilbert.ContourInverseBounds
import ComputableAnalysis.RiemannHilbert.ReciprocalDifference

/-! Quantitative reciprocal perturbation from a supplied bound, independent
of the search evaluator's initial box. Actual inverse names are compared. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions RepresentedReciprocal
set_option autoImplicit false

theorem inverse_near_exists_bound (a z : Scalar) (ha : NonzeroBoxSearch.Nonzero a)
    (B H : Rat) (hB : 0≤B) (hH : 0≤H)
    (hA : Small (inverse a ha).val B) (hza : Small (sub z.val a.val) H)
    (hbudget : 16*B*H≤1) :
    ∃ hz : NonzeroBoxSearch.Nonzero z, Small (inverse z hz).val (8*B) := by
  let s := ReciprocalLocalBounds.normalized a ha z
  have hs : Small (sub (ofQComplex QComplex.one) s.val) ((1:Rat)/8) := by
    have hm := SeriesLimitLaws.small_neg (Small.mul (inverse a ha).property
      (sub_valid z.property a.property) hB hH hA hza)
    exact Small.congr (neg_valid (mul_valid (inverse a ha).property (sub_valid z.property a.property)))
      (sub_valid (ofQComplex_valid _) s.property)
      (equiv_symm (ReciprocalLocalBounds.residual a ha z)) (hm.mono (by grind only))
  let r := ScalarNeumannInverse.value s hs
  let v := scalarProduct (inverse a ha) r
  have hv : (mul z.val v.val).Equiv (ofQComplex QComplex.one) := by
    have hu := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := mul_valid s.property r.property) (hright := ofQComplex_valid _)
      (ScalarNeumannInverse.mul_value s hs)
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid z.property v.property) (hright := ofQComplex_valid _)
    change (gridScalarValue (inverse a ha)*gridScalarValue z)*gridScalarValue r=1 at hu
    change gridScalarValue z*(gridScalarValue (inverse a ha)*gridScalarValue r)=1
    grind only
  let hz := nonzero_of_inverse z v hv
  refine ⟨hz, ?_⟩
  have hm := Small.mul (inverse a ha).property r.property hB (by decide +kernel)
    hA (ScalarNeumannInverse.value_bound s hs)
  have he : 2*B*4=8*B := by grind only
  rw [he] at hm
  exact Small.congr v.property (inverse z hz).property
    (equiv_symm (inverse_unique z hz v hv)) hm

theorem inverse_near_difference_bound (a z : Scalar)
    (ha : NonzeroBoxSearch.Nonzero a) (hz : NonzeroBoxSearch.Nonzero z)
    (B H : Rat) (hB : 0≤B) (hH : 0≤H)
    (hA : Small (inverse a ha).val B) (hza : Small (sub z.val a.val) H)
    (hbudget : 16*B*H≤1) :
    Small (sub (inverse z hz).val (inverse a ha).val) (32*B*B*H) := by
  obtain ⟨hz',hZ⟩ := inverse_near_exists_bound a z ha B H hB hH hA hza hbudget
  have hZ' : Small (inverse z hz).val (8*B) := hZ
  have hm := SeriesLimitLaws.small_neg (Small.mul
    (mul_valid (inverse a ha).property (sub_valid z.property a.property))
    (inverse z hz).property (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hB) hH)
    (Rat.mul_nonneg (by decide +kernel) hB)
    (Small.mul (inverse a ha).property (sub_valid z.property a.property) hB hH hA hza) hZ')
  have he : 2*(2*B*H)*(8*B)=32*B*B*H := by grind only
  rw [he] at hm
  exact Small.congr
    (neg_valid (mul_valid (mul_valid (inverse a ha).property (sub_valid z.property a.property))
      (inverse z hz).property))
    (sub_valid (inverse z hz).property (inverse a ha).property)
    (equiv_symm (ReciprocalDifference.difference a z ha hz)) hm

theorem offset_difference_self (d w : Scalar) :
    (sub (Centered.offset d w).val w.val).Equiv (neg d.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (Centered.offset d w).property w.property) (hright := neg_valid d.property)
  change (gridScalarValue w-gridScalarValue d)-gridScalarValue w= -gridScalarValue d
  grind only

theorem frame_reciprocal_displacement_bound (R : QPos) (d : Scalar)
    (H : Rat) (hH : 0≤H) (hHR : H≤R.val/64) (hd : Small d.val H)
    (q : QComplex) (hq : frameDomain R (rationalRectangleScalar q))
    (hz : NonzeroBoxSearch.Nonzero (Centered.offset d (rationalRectangleScalar q))) :
    Small (sub (inverse (Centered.offset d (rationalRectangleScalar q)) hz).val
      (inverse (rationalRectangleScalar q) (frameDomain_nonzero R _ hq)).val)
      (128*H/(R.val*R.val)) := by
  let w := rationalRectangleScalar q
  let z := Centered.offset d w
  have hza : Small (sub z.val w.val) H :=
    Small.congr (neg_valid d.property) (sub_valid z.property w.property)
      (equiv_symm (offset_difference_self d w)) (SeriesLimitLaws.small_neg hd)
  have hB : 0≤2/R.val := by
    rw [Rat.div_def]; exact Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr R.property))
  have hi := Rat.mul_inv_cancel R.val (Rat.ne_of_gt R.property)
  have hb : 16*(2/R.val)*H≤1 := by
    have hm := Rat.mul_le_mul_of_nonneg_left hHR
      (Rat.mul_nonneg (show (0:Rat)≤16 by decide +kernel) hB)
    simp only [Rat.div_def] at hm ⊢
    grind only
  have hs := inverse_near_difference_bound w z (frameDomain_nonzero R _ hq) hz
    (2/R.val) H hB hH (frame_rational_inverse_bound R q hq _) hza hb
  have he : 32*(2/R.val)*(2/R.val)*H=128*H/(R.val*R.val) := by
    simp only [Rat.div_def,Rat.inv_mul_rev]; grind only
  rw [he] at hs
  exact hs

end ComputableAnalysis.RiemannHilbert.RectangularContour
