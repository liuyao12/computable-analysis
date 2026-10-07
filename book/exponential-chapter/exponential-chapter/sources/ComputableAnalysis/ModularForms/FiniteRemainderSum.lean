import ComputableAnalysis.ModularForms.PairedRemainderAgreement

/-! Exact finite summation of actual derivative remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem finiteRemainderSum (f g d : Nat → ComplexRaw)
    (hf : ∀ n, (f n).Valid) (hg : ∀ n, (g n).Valid) (hd : ∀ n, (d n).Valid)
    (h : ComplexRaw) (hh : h.Valid) (N k : Nat) :
    (ScalarSeries.block (fun n => SeriesLimitLaws.remainder (f n) (g n) (d n) h) N k).Equiv
      (SeriesLimitLaws.remainder (ScalarSeries.block f N k) (ScalarSeries.block g N k)
        (ScalarSeries.block d N k) h) := by
  have ht (n : Nat) := SeriesLimitLaws.remainder_valid (f n) (g n) (d n) h (hf n) (hg n) (hd n) hh
  induction k with
  | zero =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ScalarSeries.block_valid _ ht N 0)
      (hright := SeriesLimitLaws.remainder_valid _ _ _ _
        (ScalarSeries.block_valid f hf N 0) (ScalarSeries.block_valid g hg N 0)
        (ScalarSeries.block_valid d hd N 0) hh)
    let H := ComplexRawQuotient.ofRaw h hh
    change 0=(0-0)-0*H
    grind only
  | succ k ih =>
    have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := ScalarSeries.block_valid _ ht N k)
      (hright := SeriesLimitLaws.remainder_valid _ _ _ _
        (ScalarSeries.block_valid f hf N k) (ScalarSeries.block_valid g hg N k)
        (ScalarSeries.block_valid d hd N k) hh) ih
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ScalarSeries.block_valid _ ht N (k+1))
      (hright := SeriesLimitLaws.remainder_valid _ _ _ _
        (ScalarSeries.block_valid f hf N (k+1)) (ScalarSeries.block_valid g hg N (k+1))
        (ScalarSeries.block_valid d hd N (k+1)) hh)
    simp only [ScalarSeries.block.eq_2]
    let R := ComplexRawQuotient.ofRaw
      (ScalarSeries.block (fun n => SeriesLimitLaws.remainder (f n) (g n) (d n) h) N k)
      (ScalarSeries.block_valid _ ht N k)
    let F := ComplexRawQuotient.ofRaw (ScalarSeries.block f N k) (ScalarSeries.block_valid f hf N k)
    let G := ComplexRawQuotient.ofRaw (ScalarSeries.block g N k) (ScalarSeries.block_valid g hg N k)
    let D := ComplexRawQuotient.ofRaw (ScalarSeries.block d N k) (ScalarSeries.block_valid d hd N k)
    let X := ComplexRawQuotient.ofRaw (f (N+k)) (hf (N+k))
    let Y := ComplexRawQuotient.ofRaw (g (N+k)) (hg (N+k))
    let Z := ComplexRawQuotient.ofRaw (d (N+k)) (hd (N+k))
    let H := ComplexRawQuotient.ofRaw h hh
    change R=(F-G)-D*H at hi
    change R+((X-Y)-Z*H)=((F+X)-(G+Y))-(D+Z)*H
    grind only

theorem pairedTailRemainderPrefix_identity (B N : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) :
    (ScalarSeries.block (pairedTailRemainderTerm B a z ha hz) 0 N).Equiv
      (SeriesLimitLaws.remainder
        (ScalarSeries.block (fun n => ((pairedReciprocalTermMap (4*B+n)).eval z hz).val) 0 N)
        (ScalarSeries.block (fun n => ((pairedReciprocalTermMap (4*B+n)).eval a ha).val) 0 N)
        (ScalarSeries.block (fun n => (pairedDerivativeTailTerm a ha B n).val) 0 N)
        (sub z.val a.val)) :=
  finiteRemainderSum _ _ _
    (fun n => ((pairedReciprocalTermMap (4*B+n)).eval z hz).property)
    (fun n => ((pairedReciprocalTermMap (4*B+n)).eval a ha).property)
    (fun n => (pairedDerivativeTailTerm a ha B n).property)
    _ (sub_valid z.property a.property) 0 N

end ComputableAnalysis.ModularForms
