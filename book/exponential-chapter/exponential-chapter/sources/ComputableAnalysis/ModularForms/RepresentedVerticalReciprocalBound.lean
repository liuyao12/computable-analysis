import ComputableAnalysis.ModularForms.RationalVerticalReciprocalBound
import ComputableAnalysis.RiemannHilbert.RepresentedReciprocal
import ComputableAnalysis.ModularForms.PairedGlobalOffPoleIntegerDomain

/-! Uniform bounds for actual represented inverses above a horizontal line. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def verticalTailRaw (z : Scalar) (N : Nat) : ComplexRaw where
  compute n := z.val.compute (N+n)

theorem verticalTailRaw_valid (z : Scalar) (N : Nat) : (verticalTailRaw z N).Valid := by
  refine ⟨fun n => z.property.1 (N+n),fun n m hnm => z.property.2.1 (N+n) (N+m) (by omega),?_⟩
  intro eps
  obtain ⟨M,hM⟩ := z.property.2.2 eps
  exact ⟨M,fun n hn => hM (N+n) (by omega)⟩

def verticalTailScalar (z : Scalar) (N : Nat) : Scalar :=
  ⟨verticalTailRaw z N,verticalTailRaw_valid z N⟩

theorem verticalTailScalar_equiv (z : Scalar) (N : Nat) :
    (verticalTailScalar z N).val.Equiv z.val := by
  intro n
  exact ComplexRaw.allStagesOverlap_of_equiv z.property z.property
    (equiv_refl _ z.property) (N+n) n

theorem representedVertical_inverse_bound_all_boxes (z : Scalar)
    (hz : NonzeroBoxSearch.Nonzero z) (eta : Rat) (heta : 0<eta)
    (him : ∀ n, eta≤(z.val.compute n).lo.im) :
    Small (RepresentedReciprocal.inverse z hz).val (8/eta) := by
  let q := ReciprocalAnchor.center z hz
  have ho := valid_ordered z.property (ReciprocalAnchor.stage z hz)
  have hc := QBox.center_mem ho
  have hq : eta≤q.im := Rat.le_trans (him _) hc.1.2
  have hb := rationalVertical_reciprocal_bounds q.re q.im eta heta hq
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

theorem representedVertical_inverse_bound (z : Scalar)
    (hz : NonzeroBoxSearch.Nonzero z) (N : Nat) (eta : Rat) (heta : 0<eta)
    (him : eta≤(z.val.compute N).lo.im) :
    Small (RepresentedReciprocal.inverse z hz).val (8/eta) := by
  let w := verticalTailScalar z N
  have hw : NonzeroBoxSearch.Nonzero w :=
    (NonzeroBoxSearch.nonzero_congr w z (verticalTailScalar_equiv z N)).mpr hz
  have hs := representedVertical_inverse_bound_all_boxes w hw eta heta
    (fun n => Rat.le_trans him (z.property.2.1 N (N+n) (by omega)).2.2.1)
  exact Small.congr (RepresentedReciprocal.inverse w hw).property
    (RepresentedReciprocal.inverse z hz).property
    (RepresentedReciprocal.inverse_congr w z hw hz (verticalTailScalar_equiv z N)) hs

theorem globalIntegerReciprocal_vertical_bound (z : Scalar) (hz : pairedOffPoleDomain z)
    (N : Nat) (eta : Rat) (heta : 0<eta)
    (him : eta≤(z.val.compute N).lo.im) (k : Int) :
    Small (globalOffPoleIntegerReciprocal z hz k).val (8/eta) := by
  apply representedVertical_inverse_bound (integerShiftScalar z k)
    (pairedOffPoleDomain_integer_nonzero z hz k) N eta heta
  simpa only [integerShiftScalar,integerAffine,translate,scaleRat,QBox.scaleRat,
    add,ofQComplex,QBox.add,QComplex.add,Rat.intCast_one,
    if_pos (show (0:Rat)≤1 by decide),Rat.one_mul,Rat.add_zero] using him

end ComputableAnalysis.ModularForms
