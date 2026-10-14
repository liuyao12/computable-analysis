import ComputableAnalysis.ModularForms.PairedDivisionDerivativeReflection

/-! Reflection symmetry survives the actual convergent derivative sum. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem block_neg (t : Nat → ComplexRaw) (ht : ∀ n, (t n).Valid) (N : Nat) :
    (ScalarSeries.block (fun n => neg (t n)) 0 N).Equiv (neg (ScalarSeries.block t 0 N)) := by
  induction N with
  | zero =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ofQComplex_valid _) (hright := neg_valid (ofQComplex_valid _))
    change (0:ComplexRawQuotient.Value)= -0
    grind only
  | succ N ih =>
    have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := ScalarSeries.block_valid _ (fun n => neg_valid (ht n)) 0 N)
      (hright := neg_valid (ScalarSeries.block_valid t ht 0 N)) ih
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ScalarSeries.block_valid _ (fun n => neg_valid (ht n)) 0 (N+1))
      (hright := neg_valid (ScalarSeries.block_valid t ht 0 (N+1)))
    let A := ComplexRawQuotient.ofRaw (ScalarSeries.block (fun n => neg (t n)) 0 N)
      (ScalarSeries.block_valid _ (fun n => neg_valid (ht n)) 0 N)
    let B := ComplexRawQuotient.ofRaw (ScalarSeries.block t 0 N) (ScalarSeries.block_valid t ht 0 N)
    let T := ComplexRawQuotient.ofRaw (t N) (ht N)
    change A= -B at hi
    simp only [ScalarSeries.block]
    rw [ComplexRawQuotient.ofRaw_add _ _
      (ScalarSeries.block_valid _ (fun n => neg_valid (ht n)) 0 N) (neg_valid (ht (0+N))),
      ComplexRawQuotient.ofRaw_neg _ (add_valid (ScalarSeries.block_valid t ht 0 N) (ht (0+N))),
      ComplexRawQuotient.ofRaw_add _ _ (ScalarSeries.block_valid t ht 0 N) (ht (0+N)),
      ComplexRawQuotient.ofRaw_neg _ (ht (0+N))]
    simp only [Nat.zero_add]
    change A+(-T)= -(B+T)
    grind only [ComplexRawQuotient.neg_add]

theorem pairedDivisionDerivativePrefix_odd (z w : Scalar)
    (hz : LocalODE.interior (1/4) z) (hw : LocalODE.interior (1/4) w)
    (he : w.val.Equiv (neg z.val)) (N : Nat) :
    (ScalarSeries.block (fun n => (pairedRegularDivisionDerivativeTerm w hw n).val) 0 N).Equiv
      (neg (ScalarSeries.block (fun n => (pairedRegularDivisionDerivativeTerm z hz n).val) 0 N)) := by
  exact equiv_trans
    (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm w hw n).property) 0 N)
    (ScalarSeries.block_valid _ (fun n => neg_valid (pairedRegularDivisionDerivativeTerm z hz n).property) 0 N)
    (neg_valid (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm z hz n).property) 0 N))
    (ScalarSeries.block_congr _ _ (fun n => pairedRegularDivisionDerivativeTerm_odd n z w hz hw he) 0 N)
    (block_neg _ (fun n => (pairedRegularDivisionDerivativeTerm z hz n).property) N)

theorem pairedRegularDivisionDerivativeValue_odd (z w : Scalar)
    (hz : LocalODE.interior (1/4) z) (hw : LocalODE.interior (1/4) w)
    (he : w.val.Equiv (neg z.val)) :
    (pairedRegularDivisionDerivativeValue w hw).Equiv (neg (pairedRegularDivisionDerivativeValue z hz)) := by
  let p := fun N => ScalarSeries.block (fun n => (pairedRegularDivisionDerivativeTerm w hw n).val) 0 (N+1)
  have hp : ∀ N, (p N).Valid := fun N => ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm w hw n).property) 0 (N+1)
  apply RepresentedCauchySum.unique p hp (fun N => 64*((N+1:Nat):Rat)⁻¹)
    (pairedReciprocalTail_shrinks 64) _ _
    (pairedRegularDivisionDerivativeValue_valid w hw) (neg_valid (pairedRegularDivisionDerivativeValue_valid z hz))
    (pairedRegularDivisionDerivativeValue_close w hw)
  intro N
  have hb := SeriesLimitLaws.small_neg (pairedRegularDivisionDerivativeValue_close z hz N)
  have hprefix := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm w hw n).property) 0 (N+1))
      (hright := neg_valid (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm z hz n).property) 0 (N+1))) (pairedDivisionDerivativePrefix_odd z w hz hw he (N+1))
  have hEq : (neg (sub (pairedRegularDivisionDerivativeValue z hz)
      (ScalarSeries.block (fun n => (pairedRegularDivisionDerivativeTerm z hz n).val) 0 (N+1)))).Equiv
      (sub (neg (pairedRegularDivisionDerivativeValue z hz)) (p N)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (sub_valid (pairedRegularDivisionDerivativeValue_valid z hz)
        (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm z hz n).property) 0 (N+1))))
      (hright := sub_valid (neg_valid (pairedRegularDivisionDerivativeValue_valid z hz)) (hp N))
    let V := ComplexRawQuotient.ofRaw (pairedRegularDivisionDerivativeValue z hz) (pairedRegularDivisionDerivativeValue_valid z hz)
    let PZ := ComplexRawQuotient.ofRaw (ScalarSeries.block (fun n => (pairedRegularDivisionDerivativeTerm z hz n).val) 0 (N+1))
      (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm z hz n).property) 0 (N+1))
    let PW := ComplexRawQuotient.ofRaw (p N) (hp N)
    change PW= -PZ at hprefix
    change -(V-PZ)=(-V)-PW
    grind only [ComplexRawQuotient.neg_add,ComplexRawQuotient.neg_neg]
  exact Small.congr (neg_valid (sub_valid (pairedRegularDivisionDerivativeValue_valid z hz)
    (ScalarSeries.block_valid _ (fun n => (pairedRegularDivisionDerivativeTerm z hz n).property) 0 (N+1))))
    (sub_valid (neg_valid (pairedRegularDivisionDerivativeValue_valid z hz)) (hp N)) hEq hb

end ComputableAnalysis.ModularForms
