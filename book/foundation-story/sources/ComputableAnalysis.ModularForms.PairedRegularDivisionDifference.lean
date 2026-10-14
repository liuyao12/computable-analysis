import ComputableAnalysis.ModularForms.PairedDenominatorDifference
import ComputableAnalysis.ModularForms.LatticeReciprocalDifference

/-! Quantitative differences of the actual regular-division terms. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedSmallDiskLiteralInverse_bound (z : Scalar) (hz : Small z.val (1/4)) (n : Nat) :
    Small (RepresentedReciprocal.inverse (pairedLiteralDenominator z (pairedIntegerSquare (n+1)))
      ((pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel) hz) n)).val
      (4*reciprocalSquare (n+1)) := by
  have hp : (1:Rat)≤((n+1:Nat):Rat) := by exact_mod_cast (show 1≤n+1 by omega)
  have hsq := Rat.mul_le_mul_of_nonneg_left hp (Rat.natCast_nonneg (a := n+1))
  have hl : 16*(1/4:Rat)*(1/4)≤pairedIntegerSquare (n+1) := by
    unfold pairedIntegerSquare; grind only
  let hd := pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel) hz
  have hc : 0≤1/pairedIntegerSquare (n+1) := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.le_of_lt (Rat.inv_pos.mpr (pairedIntegerSquare_pos _ (by omega)))
  have ht : pairedIntegerSquare (n+1)*(1/pairedIntegerSquare (n+1))=1 := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.mul_inv_cancel _ (Rat.ne_of_gt (pairedIntegerSquare_pos _ (by omega)))
  have hb := pairedLiteralInverse_bound z (1/4) (1/pairedIntegerSquare (n+1)) (pairedIntegerSquare (n+1))
    (by decide +kernel) hc hz (pairedInteger_normalization (1/4) (n+1) (by omega) hl) ht (hd n)
  simpa only [reciprocalSquare,pairedIntegerSquare,Rat.div_def,Rat.one_mul] using hb

theorem pairedRegularDivisionTerm_difference_bound (a z : Scalar)
    (ha : Small a.val (1/4)) (hz : Small z.val (1/4)) (H : Rat)
    (hH : 0≤H) (hd : Small (sub z.val a.val) H) (n : Nat) :
    Small (sub (pairedRegularDivisionTerm z hz n).val (pairedRegularDivisionTerm a ha n).val)
      (128*H*reciprocalSquare (n+1)*reciprocalSquare (n+1)) := by
  let da := pairedSmallDisk_domain a (1/4) (by decide +kernel) (by decide +kernel) ha
  let dz := pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel) hz
  have hp : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  have hc : 0≤reciprocalSquare (n+1) := by
    unfold reciprocalSquare
    exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp))
  have hd' := pairedLiteralDenominator_difference_bound a z ha hz (pairedIntegerSquare (n+1)) H hH hd
  have hi := pairedBoundaryReciprocal_difference_bound
    (pairedLiteralDenominator z (pairedIntegerSquare (n+1)))
    (pairedLiteralDenominator a (pairedIntegerSquare (n+1))) (dz n) (da n)
    H (4*reciprocalSquare (n+1)) (4*reciprocalSquare (n+1)) hH
    (Rat.mul_nonneg (by decide) hc) (Rat.mul_nonneg (by decide) hc)
    (RepresentedCauchySum.small_sub_symm _ _ _ hd')
    (pairedSmallDiskLiteralInverse_bound z hz n) (pairedSmallDiskLiteralInverse_bound a ha n)
  have hs := LocalODE.small_scale (show (0:Rat)≤2 by decide) hi
  have he : (scaleRat 2 (sub
      (RepresentedReciprocal.inverse (pairedLiteralDenominator z (pairedIntegerSquare (n+1))) (dz n)).val
      (RepresentedReciprocal.inverse (pairedLiteralDenominator a (pairedIntegerSquare (n+1))) (da n)).val)).Equiv
      (sub (pairedRegularDivisionTerm z hz n).val (pairedRegularDivisionTerm a ha n).val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := scaleRat_valid (sub_valid (RepresentedReciprocal.inverse _ (dz n)).property
        (RepresentedReciprocal.inverse _ (da n)).property))
      (hright := sub_valid (pairedRegularDivisionTerm z hz n).property (pairedRegularDivisionTerm a ha n).property)
    let I := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse _ (dz n)).val (RepresentedReciprocal.inverse _ (dz n)).property
    let J := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse _ (da n)).val (RepresentedReciprocal.inverse _ (da n)).property
    change ComplexRawQuotient.scaleRat 2 (I-J)=ComplexRawQuotient.scaleRat 2 I-ComplexRawQuotient.scaleRat 2 J
    have hs : I-J=I+(-J) := by grind only
    rw [hs,ComplexRawQuotient.scaleRat_add,ComplexRawQuotient.neg_eq_scaleRat_neg_one,
      ComplexRawQuotient.scaleRat_scaleRat]
    have hn := ComplexRawQuotient.neg_scaleRat 2 J
    rw [show (2:Rat)*(-1)= -2 by decide +kernel]
    grind only
  have hb := Small.congr (scaleRat_valid (sub_valid (RepresentedReciprocal.inverse _ (dz n)).property
      (RepresentedReciprocal.inverse _ (da n)).property))
    (sub_valid (pairedRegularDivisionTerm z hz n).property (pairedRegularDivisionTerm a ha n).property) he hs
  exact hb.mono (by grind only)

end ComputableAnalysis.ModularForms
