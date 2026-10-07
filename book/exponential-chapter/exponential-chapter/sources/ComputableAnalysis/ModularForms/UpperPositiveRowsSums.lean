import ComputableAnalysis.ModularForms.UpperPositiveRowBounds
import ComputableAnalysis.ModularForms.IntegerPowerRemainderTail

/-! Constructed sums of actual positive lattice rows in weights four and six. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem fourConstant_nonneg (z : Scalar) (hz : InUpperHalfPlane z.val) :
    0≤upperWeightFourTailConstant z hz := by
  unfold upperWeightFourTailConstant
  exact Rat.mul_nonneg (by decide +kernel)
    (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) (latticeReciprocalConstant_nonnegative z hz)))

private theorem sixConstant_nonneg (z : Scalar) (hz : InUpperHalfPlane z.val) :
    0≤upperWeightSixTailConstant z hz := by
  unfold upperWeightSixTailConstant
  exact Rat.mul_nonneg (by decide +kernel)
    (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) (latticeReciprocalConstant_nonnegative z hz)))

/-- The tail of actual infinite positive rows, starting at height two. -/
def upperPositiveWeightFourRowsTail (z : Scalar) (hz : InUpperHalfPlane z.val) : ComplexRaw :=
  RepresentedCauchySum.value
    (fun N => ScalarSeries.block (fun n => (upperPositiveLatticeRowSum z hz 4 (by omega) (n+1)).val) 0 (N+1))
    (fun N => ScalarSeries.block_valid _ (fun n => (upperPositiveLatticeRowSum z hz 4 (by omega) (n+1)).property) 0 (N+1))
    (fun N => upperWeightFourTailConstant z hz*(((N+1:Nat):Rat))⁻¹)

def upperPositiveWeightSixRowsTail (z : Scalar) (hz : InUpperHalfPlane z.val) : ComplexRaw :=
  RepresentedCauchySum.value
    (fun N => ScalarSeries.block (fun n => (upperPositiveLatticeRowSum z hz 6 (by omega) (n+1)).val) 0 (N+1))
    (fun N => ScalarSeries.block_valid _ (fun n => (upperPositiveLatticeRowSum z hz 6 (by omega) (n+1)).property) 0 (N+1))
    (fun N => upperWeightSixTailConstant z hz*(((N+1:Nat):Rat))⁻¹)

theorem upperPositiveWeightFourRowsTail_valid (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (upperPositiveWeightFourRowsTail z hz).Valid :=
  RepresentedCauchySum.value_valid _ _ _
    (rationalInverseSquareRate_shrinks _ (fourConstant_nonneg z hz))
    (rationalInverseSquare_prefix_cauchy _
      (fun n => (upperPositiveLatticeRowSum z hz 4 (by omega) (n+1)).property) _ (fourConstant_nonneg z hz)
      (upperPositiveLatticeRowSum_weightFour_bound z hz))

theorem upperPositiveWeightSixRowsTail_valid (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (upperPositiveWeightSixRowsTail z hz).Valid :=
  RepresentedCauchySum.value_valid _ _ _
    (rationalInverseSquareRate_shrinks _ (sixConstant_nonneg z hz))
    (rationalInverseSquare_prefix_cauchy _
      (fun n => (upperPositiveLatticeRowSum z hz 6 (by omega) (n+1)).property) _ (sixConstant_nonneg z hz)
      (upperPositiveLatticeRowSum_weightSix_bound z hz))

theorem upperPositiveWeightFourRowsTail_close (z : Scalar) (hz : InUpperHalfPlane z.val) (N : Nat) :
    Small (sub (upperPositiveWeightFourRowsTail z hz)
      (ScalarSeries.block (fun n => (upperPositiveLatticeRowSum z hz 4 (by omega) (n+1)).val) 0 (N+1)))
      (upperWeightFourTailConstant z hz*(((N+1:Nat):Rat))⁻¹) :=
  RepresentedCauchySum.value_close_prefix _ _ _
    (rationalInverseSquare_prefix_cauchy _
      (fun n => (upperPositiveLatticeRowSum z hz 4 (by omega) (n+1)).property) _ (fourConstant_nonneg z hz)
      (upperPositiveLatticeRowSum_weightFour_bound z hz)) N

theorem upperPositiveWeightSixRowsTail_close (z : Scalar) (hz : InUpperHalfPlane z.val) (N : Nat) :
    Small (sub (upperPositiveWeightSixRowsTail z hz)
      (ScalarSeries.block (fun n => (upperPositiveLatticeRowSum z hz 6 (by omega) (n+1)).val) 0 (N+1)))
      (upperWeightSixTailConstant z hz*(((N+1:Nat):Rat))⁻¹) :=
  RepresentedCauchySum.value_close_prefix _ _ _
    (rationalInverseSquare_prefix_cauchy _
      (fun n => (upperPositiveLatticeRowSum z hz 6 (by omega) (n+1)).property) _ (sixConstant_nonneg z hz)
      (upperPositiveLatticeRowSum_weightSix_bound z hz)) N

/-- The first row plus the justified, convergent tail of all later positive rows. -/
def upperPositiveWeightFourRowsSum (z : Scalar) (hz : InUpperHalfPlane z.val) : ComplexRaw :=
  add (upperPositiveLatticeRowSum z hz 4 (by omega) 0).val (upperPositiveWeightFourRowsTail z hz)

def upperPositiveWeightSixRowsSum (z : Scalar) (hz : InUpperHalfPlane z.val) : ComplexRaw :=
  add (upperPositiveLatticeRowSum z hz 6 (by omega) 0).val (upperPositiveWeightSixRowsTail z hz)

theorem upperPositiveWeightFourRowsSum_valid (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (upperPositiveWeightFourRowsSum z hz).Valid :=
  add_valid (upperPositiveLatticeRowSum z hz 4 (by omega) 0).property
    (upperPositiveWeightFourRowsTail_valid z hz)

theorem upperPositiveWeightSixRowsSum_valid (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (upperPositiveWeightSixRowsSum z hz).Valid :=
  add_valid (upperPositiveLatticeRowSum z hz 6 (by omega) 0).property
    (upperPositiveWeightSixRowsTail_valid z hz)

private theorem inverseSquareNames_congr (t u : Nat → ComplexRaw)
    (ht : ∀ n, (t n).Valid) (hu : ∀ n, (u n).Valid) (C D : Rat)
    (hC : 0≤C) (hD : 0≤D)
    (hB : ∀ n, Small (t n) (C*reciprocalSquare (n+1)))
    (hU : ∀ n, Small (u n) (D*reciprocalSquare (n+1)))
    (he : ∀ n, (t n).Equiv (u n)) :
    (RepresentedCauchySum.value (fun N => ScalarSeries.block t 0 (N+1))
      (fun N => ScalarSeries.block_valid t ht 0 (N+1))
      (fun N => C*(((N+1:Nat):Rat))⁻¹)).Equiv
    (RepresentedCauchySum.value (fun N => ScalarSeries.block u 0 (N+1))
      (fun N => ScalarSeries.block_valid u hu 0 (N+1))
      (fun N => D*(((N+1:Nat):Rat))⁻¹)) := by
  have hi (N : Nat) : (0:Rat)≤(((N+1:Nat):Rat))⁻¹ :=
    Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (show 0<N+1 by omega)))
  exact RepresentedCauchySum.value_congr _ _ _ _ _ _
    (rationalInverseSquareRate_shrinks C hC) (rationalInverseSquareRate_shrinks D hD)
    (fun N => Rat.mul_nonneg hC (hi N)) (fun N => Rat.mul_nonneg hD (hi N))
    (rationalInverseSquare_prefix_cauchy t ht C hC hB)
    (rationalInverseSquare_prefix_cauchy u hu D hD hU)
    (fun N => ScalarSeries.block_congr t u he 0 (N+1))

/-- The independently chosen tail constants do not affect the represented sum. -/
theorem upperPositiveWeightFourRowsTail_congr (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val) (he : z.val.Equiv w.val) :
    (upperPositiveWeightFourRowsTail z hz).Equiv (upperPositiveWeightFourRowsTail w hw) :=
  inverseSquareNames_congr _ _
    (fun n => (upperPositiveLatticeRowSum z hz 4 (by omega) (n+1)).property)
    (fun n => (upperPositiveLatticeRowSum w hw 4 (by omega) (n+1)).property)
    (upperWeightFourTailConstant z hz) (upperWeightFourTailConstant w hw)
    (fourConstant_nonneg z hz) (fourConstant_nonneg w hw)
    (upperPositiveLatticeRowSum_weightFour_bound z hz) (upperPositiveLatticeRowSum_weightFour_bound w hw)
    (fun n => upperPositiveLatticeRowSum_congr z w hz hw he 4 (by omega) (n+1))

theorem upperPositiveWeightSixRowsTail_congr (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val) (he : z.val.Equiv w.val) :
    (upperPositiveWeightSixRowsTail z hz).Equiv (upperPositiveWeightSixRowsTail w hw) :=
  inverseSquareNames_congr _ _
    (fun n => (upperPositiveLatticeRowSum z hz 6 (by omega) (n+1)).property)
    (fun n => (upperPositiveLatticeRowSum w hw 6 (by omega) (n+1)).property)
    (upperWeightSixTailConstant z hz) (upperWeightSixTailConstant w hw)
    (sixConstant_nonneg z hz) (sixConstant_nonneg w hw)
    (upperPositiveLatticeRowSum_weightSix_bound z hz) (upperPositiveLatticeRowSum_weightSix_bound w hw)
    (fun n => upperPositiveLatticeRowSum_congr z w hz hw he 6 (by omega) (n+1))

theorem upperPositiveWeightFourRowsSum_congr (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val) (he : z.val.Equiv w.val) :
    (upperPositiveWeightFourRowsSum z hz).Equiv (upperPositiveWeightFourRowsSum w hw) :=
  add_equiv (upperPositiveLatticeRowSum_congr z w hz hw he 4 (by omega) 0)
    (upperPositiveWeightFourRowsTail_congr z w hz hw he)

theorem upperPositiveWeightSixRowsSum_congr (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val) (he : z.val.Equiv w.val) :
    (upperPositiveWeightSixRowsSum z hz).Equiv (upperPositiveWeightSixRowsSum w hw) :=
  add_equiv (upperPositiveLatticeRowSum_congr z w hz hw he 6 (by omega) 0)
    (upperPositiveWeightSixRowsTail_congr z w hz hw he)

end ComputableAnalysis.ModularForms
