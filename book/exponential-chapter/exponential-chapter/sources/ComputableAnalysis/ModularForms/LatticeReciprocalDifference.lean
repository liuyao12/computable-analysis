import ComputableAnalysis.ModularForms.PairedLatticePrefixes

/-! Exact reciprocal differences for lattice reindexing boundary estimates. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedBoundaryReciprocal_difference (z w : Scalar)
    (hz : NonzeroBoxSearch.Nonzero z) (hw : NonzeroBoxSearch.Nonzero w) :
    (sub (RepresentedReciprocal.inverse z hz).val (RepresentedReciprocal.inverse w hw).val).Equiv
      (mul (sub w.val z.val)
        (mul (RepresentedReciprocal.inverse z hz).val (RepresentedReciprocal.inverse w hw).val)) := by
  let I := RepresentedReciprocal.inverse z hz
  let J := RepresentedReciprocal.inverse w hw
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid z.property I.property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse z hz)
  have hj := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid w.property J.property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse w hw)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := sub_valid I.property J.property)
    (hright := mul_valid (sub_valid w.property z.property) (mul_valid I.property J.property))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let W := ComplexRawQuotient.ofRaw w.val w.property
  let A := ComplexRawQuotient.ofRaw I.val I.property
  let B := ComplexRawQuotient.ofRaw J.val J.property
  change Z*A=1 at hi
  change W*B=1 at hj
  change A-B=(W-Z)*(A*B)
  grind only

theorem pairedBoundaryReciprocal_difference_bound (z w : Scalar)
    (hz : NonzeroBoxSearch.Nonzero z) (hw : NonzeroBoxSearch.Nonzero w) (H M N : Rat)
    (hH : 0≤H) (hM : 0≤M) (hN : 0≤N) (hd : Small (sub w.val z.val) H)
    (hi : Small (RepresentedReciprocal.inverse z hz).val M)
    (hj : Small (RepresentedReciprocal.inverse w hw).val N) :
    Small (sub (RepresentedReciprocal.inverse z hz).val (RepresentedReciprocal.inverse w hw).val)
      (4*H*M*N) := by
  have vi := (RepresentedReciprocal.inverse z hz).property
  have vj := (RepresentedReciprocal.inverse w hw).property
  have hp := Small.mul vi vj hM hN hi hj
  have hb := Small.mul (sub_valid w.property z.property) (mul_valid vi vj) hH
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hN) hd hp
  rw [show (2:Rat)*H*(2*M*N)=4*H*M*N by grind only] at hb
  exact Small.congr (mul_valid (sub_valid w.property z.property) (mul_valid vi vj))
    (sub_valid vi vj) (equiv_symm (pairedBoundaryReciprocal_difference z w hz hw)) hb

end ComputableAnalysis.ModularForms
