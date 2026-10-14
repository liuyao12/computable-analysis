import ComputableAnalysis.ModularForms.PairedReciprocalSquarePrefixes

/-! Constructed reciprocal-square tails with explicit errors and derivative agreement. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem inverseSquareSeriesValue_neg (t : Nat → ComplexRaw) (ht : ∀ n, (t n).Valid)
    (C : Nat) (hB : ∀ n, Small (t n) ((C:Rat)*reciprocalSquare (n+1))) :
    (inverseSquareSeriesValue (fun n => neg (t n)) (fun n => neg_valid (ht n)) C).Equiv
      (neg (inverseSquareSeriesValue t ht C)) := by
  have hneg n := SeriesLimitLaws.small_neg (hB n)
  apply RepresentedCauchySum.unique
    (fun N => ScalarSeries.block (fun n => neg (t n)) 0 (N+1))
    (fun N => ScalarSeries.block_valid _ (fun n => neg_valid (ht n)) 0 (N+1))
    (fun N => (C:Rat)*(((N+1:Nat):Rat))⁻¹) (pairedReciprocalTail_shrinks C)
    _ _ (inverseSquareSeriesValue_valid _ _ C hneg)
    (neg_valid (inverseSquareSeriesValue_valid t ht C hB))
    (inverseSquareSeriesValue_close _ _ C hneg) ?_
  intro N
  let s := inverseSquareSeriesValue t ht C
  let p := ScalarSeries.block t 0 (N+1)
  let q := ScalarSeries.block (fun n => neg (t n)) 0 (N+1)
  have vs := inverseSquareSeriesValue_valid t ht C hB
  have vp := ScalarSeries.block_valid t ht 0 (N+1)
  have vq := ScalarSeries.block_valid _ (fun n => neg_valid (ht n)) 0 (N+1)
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := vq) (hright := neg_valid vp)
    (reciprocalSquare_block_neg t ht (N+1))
  have he : (neg (sub s p)).Equiv (sub (neg s) q) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (sub_valid vs vp)) (hright := sub_valid (neg_valid vs) vq)
    let S := ComplexRawQuotient.ofRaw s vs
    let P := ComplexRawQuotient.ofRaw p vp
    let Q := ComplexRawQuotient.ofRaw q vq
    change Q= -P at hp
    change -(S-P)= -S-Q
    generalize S=a, P=b, Q=c at hp ⊢
    grind only
  exact Small.congr (neg_valid (sub_valid vs vp)) (sub_valid (neg_valid vs) vq) he
    (SeriesLimitLaws.small_neg (inverseSquareSeriesValue_close t ht C hB N))

def pairedReciprocalSquareTailTerm (z : Scalar) (hz : InUpperHalfPlane z.val) (B n : Nat) : Scalar :=
  upperPairedReciprocalSquare z hz (pairedTailShift B n)

theorem pairedReciprocalSquareTailTerm_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hB : Small z.val (B:Rat)) (n : Nat) :
    Small (pairedReciprocalSquareTailTerm z hz B n).val
      (((1024:Nat):Rat)*reciprocalSquare (n+1)) :=
  Small.congr (neg_valid (pairedDerivativeTailTerm z hz B n).property)
    (pairedReciprocalSquareTailTerm z hz B n).property
    (equiv_symm (upperPairedReciprocalSquare_derivative z hz (pairedTailShift B n)))
    (SeriesLimitLaws.small_neg (pairedDerivativeTailTerm_bound z hz B hB n))

def pairedReciprocalSquareTailValue (z : Scalar) (hz : InUpperHalfPlane z.val) (B : Nat) : ComplexRaw :=
  inverseSquareSeriesValue (fun n => (pairedReciprocalSquareTailTerm z hz B n).val)
    (fun n => (pairedReciprocalSquareTailTerm z hz B n).property) 1024

theorem pairedReciprocalSquareTailValue_valid (z : Scalar) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hB : Small z.val (B:Rat)) : (pairedReciprocalSquareTailValue z hz B).Valid :=
  inverseSquareSeriesValue_valid _ _ 1024 (pairedReciprocalSquareTailTerm_bound z hz B hB)

theorem pairedReciprocalSquareTailValue_close (z : Scalar) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hB : Small z.val (B:Rat)) (N : Nat) :
    Small (sub (pairedReciprocalSquareTailValue z hz B)
      (ScalarSeries.block (fun n => (pairedReciprocalSquareTailTerm z hz B n).val) 0 (N+1)))
      (((1024:Nat):Rat)*(((N+1:Nat):Rat))⁻¹) :=
  inverseSquareSeriesValue_close _ _ 1024 (pairedReciprocalSquareTailTerm_bound z hz B hB) N

theorem pairedReciprocalSquareTailValue_derivative (z : Scalar) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hB : Small z.val (B:Rat)) :
    (pairedReciprocalSquareTailValue z hz B).Equiv (neg (pairedDerivativeTailValue z hz B)) := by
  have he := inverseSquareSeriesValue_congr
    (fun n => (pairedReciprocalSquareTailTerm z hz B n).val)
    (fun n => neg (pairedDerivativeTailTerm z hz B n).val)
    (fun n => (pairedReciprocalSquareTailTerm z hz B n).property)
    (fun n => neg_valid (pairedDerivativeTailTerm z hz B n).property) 1024
    (pairedReciprocalSquareTailTerm_bound z hz B hB)
    (fun n => SeriesLimitLaws.small_neg (pairedDerivativeTailTerm_bound z hz B hB n))
    (fun n => upperPairedReciprocalSquare_derivative z hz (pairedTailShift B n))
  exact equiv_trans (pairedReciprocalSquareTailValue_valid z hz B hB)
    (inverseSquareSeriesValue_valid _ _ 1024
      (fun n => SeriesLimitLaws.small_neg (pairedDerivativeTailTerm_bound z hz B hB n)))
    (neg_valid (pairedDerivativeTailValue_valid z hz B hB)) he
    (inverseSquareSeriesValue_neg _ _ 1024 (pairedDerivativeTailTerm_bound z hz B hB))

end ComputableAnalysis.ModularForms
