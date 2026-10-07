import ComputableAnalysis.ModularForms.RepresentedHorizontalReciprocalBound

/-! Horizontal decay at the negative end of the actual integer reciprocal family. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem rationalNegativeHorizontal_reciprocal_bounds (a b eta : Rat)
    (heta : 0<eta) (ha : a≤ -eta) :
    (-(1/eta)≤a/(a*a+b*b) ∧ a/(a*a+b*b)≤1/eta) ∧
    (-(1/eta)≤ -b/(a*a+b*b) ∧ -b/(a*a+b*b)≤1/eta) := by
  have h := rationalHorizontal_reciprocal_bounds (-a) b eta heta (by grind only)
  constructor <;> constructor <;> grind [Rat.div_def]

theorem representedNegativeHorizontal_inverse_bound_all_boxes (z : Scalar)
    (hz : NonzeroBoxSearch.Nonzero z) (eta : Rat) (heta : 0<eta)
    (hre : ∀ n, (z.val.compute n).hi.re≤ -eta) :
    Small (RepresentedReciprocal.inverse z hz).val (8/eta) := by
  let q := ReciprocalAnchor.center z hz
  have ho := valid_ordered z.property (ReciprocalAnchor.stage z hz)
  have hc := QBox.center_mem ho
  have hq : q.re≤ -eta := Rat.le_trans hc.2.1 (hre _)
  have hb := rationalNegativeHorizontal_reciprocal_bounds q.re q.im eta heta hq
  have ha : Small (ReciprocalAnchor.anchor z hz).val (1/eta) := by
    change Small (ofQComplex (RationalReciprocal.inverse q)) (1/eta)
    refine ⟨?_,?_,?_,?_⟩ <;> intro n m
    · exact hb.1.1
    · exact hb.1.2
    · exact hb.2.1
    · exact hb.2.2
  have he : 0≤1/eta := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr heta))
  have hs := Small.mul (ReciprocalAnchor.anchor z hz).property
    (ScalarNeumannInverse.value (ReciprocalAnchor.normalized z hz)
      (ReciprocalAnchor.residual_small z hz)).property
    he (by decide +kernel) ha
    (ScalarNeumannInverse.value_bound _ _)
  exact hs.mono (by grind [Rat.div_def])

theorem representedNegativeHorizontal_inverse_bound (z : Scalar)
    (hz : NonzeroBoxSearch.Nonzero z) (N : Nat) (eta : Rat) (heta : 0<eta)
    (hre : (z.val.compute N).hi.re≤ -eta) :
    Small (RepresentedReciprocal.inverse z hz).val (8/eta) := by
  let w := verticalTailScalar z N
  have hw : NonzeroBoxSearch.Nonzero w :=
    (NonzeroBoxSearch.nonzero_congr w z (verticalTailScalar_equiv z N)).mpr hz
  have hs := representedNegativeHorizontal_inverse_bound_all_boxes w hw eta heta
    (fun n => Rat.le_trans (z.property.2.1 N (N+n) (by omega)).2.1 hre)
  exact Small.congr (RepresentedReciprocal.inverse w hw).property
    (RepresentedReciprocal.inverse z hz).property
    (RepresentedReciprocal.inverse_congr w z hw hz (verticalTailScalar_equiv z N)) hs

theorem globalIntegerReciprocal_negative_horizontal_bound (z : Scalar) (hz : pairedOffPoleDomain z)
    (N : Nat) (eta : Rat) (heta : 0<eta) (k : Int)
    (hre : (z.val.compute N).hi.re+(k:Rat)≤ -eta) :
    Small (globalOffPoleIntegerReciprocal z hz k).val (8/eta) := by
  apply representedNegativeHorizontal_inverse_bound (integerShiftScalar z k)
    (pairedOffPoleDomain_integer_nonzero z hz k) N eta heta
  simpa only [integerShiftScalar,integerAffine,translate,scaleRat,QBox.scaleRat,
    add,ofQComplex,QBox.add,QComplex.add,Rat.intCast_one,
    if_pos (show (0:Rat)≤1 by decide),Rat.one_mul] using hre

theorem globalIntegerReciprocal_negative_index_decay (z : Scalar) (hz : pairedOffPoleDomain z)
    (N : Nat) (R : Rat) (hre : (z.val.compute N).hi.re≤R)
    (n : Nat) (hn : 0<n) (hlarge : 2*R≤(n:Rat)) :
    Small (globalOffPoleIntegerReciprocal z hz (-(n:Int))).val (16/(n:Rat)) := by
  have hnq : (0:Rat)<(n:Rat) := by exact_mod_cast hn
  have he : 0<(n:Rat)/2 := by
    rw [Rat.div_def]
    exact Rat.mul_pos hnq (Rat.inv_pos.mpr (by decide +kernel))
  have hs := globalIntegerReciprocal_negative_horizontal_bound z hz N ((n:Rat)/2) he (-(n:Int))
    (show (z.val.compute N).hi.re+((-(n:Int)):Rat)≤ -((n:Rat)/2) by
      rw [Rat.intCast_natCast]
      grind only)
  have h1 := Rat.mul_inv_cancel (n:Rat) (Rat.ne_of_gt hnq)
  have h2 := Rat.mul_inv_cancel ((n:Rat)/2) (Rat.ne_of_gt he)
  apply hs.mono
  apply Rat.le_of_mul_le_mul_right (c := (n:Rat)/2) _ he
  simp only [Rat.div_def] at h1 h2 ⊢
  grind only

end ComputableAnalysis.ModularForms
