import ComputableAnalysis.ModularForms.UpperPositiveRowsSums

/-! Certified canonical prefixes for the constructed sums of all positive lattice rows. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem prefix_first (t : Nat → ComplexRaw) (ht : ∀ n, (t n).Valid) (N : Nat) :
    (ScalarSeries.block t 0 (N+1)).Equiv
      (add (t 0) (ScalarSeries.block (fun n => t (n+1)) 0 N)) := by
  induction N with
  | zero =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ScalarSeries.block_valid t ht 0 1)
      (hright := add_valid (ht 0) (ofQComplex_valid _))
    change (0:ScalarAlgebra.Value)+ComplexRawQuotient.ofRaw (t 0) (ht 0)=
      ComplexRawQuotient.ofRaw (t 0) (ht 0)+0
    grind only
  | succ N ih =>
    have hI := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := ScalarSeries.block_valid t ht 0 (N+1))
      (hright := add_valid (ht 0) (ScalarSeries.block_valid _ (fun n => ht (n+1)) 0 N)) ih
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ScalarSeries.block_valid t ht 0 (N+1+1))
      (hright := add_valid (ht 0) (ScalarSeries.block_valid _ (fun n => ht (n+1)) 0 (N+1)))
    simp only [ScalarSeries.block.eq_2,Nat.zero_add]
    let A := ComplexRawQuotient.ofRaw (t 0) (ht 0)
    let P := ComplexRawQuotient.ofRaw (add (ScalarSeries.block t 0 N) (t N))
      (add_valid (ScalarSeries.block_valid t ht 0 N) (ht N))
    let Q := ComplexRawQuotient.ofRaw (ScalarSeries.block (fun n => t (n+1)) 0 N)
      (ScalarSeries.block_valid _ (fun n => ht (n+1)) 0 N)
    let X := ComplexRawQuotient.ofRaw (t (N+1)) (ht (N+1))
    simp only [ScalarSeries.block.eq_2,Nat.zero_add] at hI
    change P=A+Q at hI
    change P+X=A+(Q+X)
    generalize P=p,A=a,Q=q,X=x at hI ⊢
    grind only

private theorem common_add_difference (a x y : ComplexRaw)
    (ha : a.Valid) (hx : x.Valid) (hy : y.Valid) :
    (sub (add a x) (add a y)).Equiv (sub x y) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (add_valid ha hx) (add_valid ha hy))
    (hright := sub_valid hx hy)
  let A := ComplexRawQuotient.ofRaw a ha
  let X := ComplexRawQuotient.ofRaw x hx
  let Y := ComplexRawQuotient.ofRaw y hy
  change (A+X)-(A+Y)=X-Y
  generalize A=a,X=x,Y=y
  grind only

private theorem common_add_close (a x y : ComplexRaw)
    (ha : a.Valid) (hx : x.Valid) (hy : y.Valid) (E : Rat)
    (he : Small (sub x y) E) : Small (sub (add a x) (add a y)) E :=
  Small.congr (sub_valid hx hy) (sub_valid (add_valid ha hx) (add_valid ha hy))
    (equiv_symm (common_add_difference a x y ha hx hy)) he

/-- The actual infinite positive-row sum is approximated by its canonical row prefixes. -/
theorem upperPositiveWeightFourRowsSum_close_prefix (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) :
    Small (sub (upperPositiveWeightFourRowsSum z hz)
      (upperPositiveLatticeRowsLimitPrefix z hz 4 (by omega) (N+2)))
      (upperWeightFourTailConstant z hz*(((N+1:Nat):Rat))⁻¹) := by
  let t := fun n => (upperPositiveLatticeRowSum z hz 4 (by omega) n).val
  have ht n : (t n).Valid := (upperPositiveLatticeRowSum z hz 4 (by omega) n).property
  let p := ScalarSeries.block (fun n => t (n+1)) 0 (N+1)
  have hp : p.Valid := ScalarSeries.block_valid _ (fun n => ht (n+1)) 0 (N+1)
  have hpre := prefix_first t ht (N+1)
  have hclose := common_add_close (t 0) (upperPositiveWeightFourRowsTail z hz) p
    (ht 0) (upperPositiveWeightFourRowsTail_valid z hz) hp _
    (upperPositiveWeightFourRowsTail_close z hz N)
  exact Small.congr
    (sub_valid (upperPositiveWeightFourRowsSum_valid z hz) (add_valid (ht 0) hp))
    (sub_valid (upperPositiveWeightFourRowsSum_valid z hz)
      (upperPositiveLatticeRowsLimitPrefix_valid z hz 4 (by omega) (N+2)))
    (FunctionTheory.sub_congr (equiv_refl _ (upperPositiveWeightFourRowsSum_valid z hz))
      (equiv_symm hpre)) hclose

theorem upperPositiveWeightSixRowsSum_close_prefix (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) :
    Small (sub (upperPositiveWeightSixRowsSum z hz)
      (upperPositiveLatticeRowsLimitPrefix z hz 6 (by omega) (N+2)))
      (upperWeightSixTailConstant z hz*(((N+1:Nat):Rat))⁻¹) := by
  let t := fun n => (upperPositiveLatticeRowSum z hz 6 (by omega) n).val
  have ht n : (t n).Valid := (upperPositiveLatticeRowSum z hz 6 (by omega) n).property
  let p := ScalarSeries.block (fun n => t (n+1)) 0 (N+1)
  have hp : p.Valid := ScalarSeries.block_valid _ (fun n => ht (n+1)) 0 (N+1)
  have hpre := prefix_first t ht (N+1)
  have hclose := common_add_close (t 0) (upperPositiveWeightSixRowsTail z hz) p
    (ht 0) (upperPositiveWeightSixRowsTail_valid z hz) hp _
    (upperPositiveWeightSixRowsTail_close z hz N)
  exact Small.congr
    (sub_valid (upperPositiveWeightSixRowsSum_valid z hz) (add_valid (ht 0) hp))
    (sub_valid (upperPositiveWeightSixRowsSum_valid z hz)
      (upperPositiveLatticeRowsLimitPrefix_valid z hz 6 (by omega) (N+2)))
    (FunctionTheory.sub_congr (equiv_refl _ (upperPositiveWeightSixRowsSum_valid z hz))
      (equiv_symm hpre)) hclose

end ComputableAnalysis.ModularForms
