import ComputableAnalysis.ModularForms.InverseSquareSeries
import ComputableAnalysis.ModularForms.PairedDerivativeTail
import ComputableAnalysis.ModularForms.PairedGlobalSecondDerivativeTail

/-! Uniform bounds for constructed inverse-square sums and actual derivative tails. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem inverseSquareBlock_split (k : Nat) :
    reciprocalSquareBlock 0 (k+1)=1+reciprocalSquareBlock 1 k := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    change reciprocalSquareBlock 0 (k+1)+reciprocalSquare (0+(k+1)+1)=
      1+(reciprocalSquareBlock 1 k+reciprocalSquare (1+k+1))
    rw [ih,show 0+(k+1)+1=1+k+1 by omega]
    grind only

theorem inverseSquareBlock_zero_bound (k : Nat) : reciprocalSquareBlock 0 k≤2 := by
  cases k with
  | zero => change (0:Rat)≤2; decide +kernel
  | succ k =>
    rw [inverseSquareBlock_split]
    have h := reciprocalSquareBlock_tail 1 k (by omega)
    rw [show ((1:Nat):Rat)⁻¹=1 by decide +kernel] at h
    grind only


theorem inverseSquareSeriesValue_bound (t : Nat → ComplexRaw)
    (ht : ∀ n, (t n).Valid) (C : Nat)
    (hB : ∀ n, Small (t n) ((C:Rat)*reciprocalSquare (n+1))) :
    Small (inverseSquareSeriesValue t ht C) (2*(C:Rat)) := by
  apply SeriesLimitLaws.small_of_prefix_bound _ (inverseSquareSeriesValue_valid t ht C hB)
    (fun N => ScalarSeries.block t 0 (N+1))
    (fun N => ScalarSeries.block_valid t ht 0 (N+1))
    (2*(C:Rat)) (fun N => (C:Rat)*((N+1:Nat):Rat)⁻¹)
    (pairedReciprocalTail_shrinks C)
  · exact inverseSquareSeriesValue_close t ht C hB
  · intro N
    apply (inverseSquare_block_bound t C hB 0 (N+1)).mono
    have h := Rat.mul_le_mul_of_nonneg_left (inverseSquareBlock_zero_bound (N+1))
      (show (0:Rat)≤(C:Rat) from Rat.natCast_nonneg)
    grind only

theorem pairedGlobalSecondDerivativeTailValue_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val) (B : Nat) (hB : Small z.val (B:Rat)) :
    Small (pairedGlobalSecondDerivativeTailValue z hz B) 131072 := by
  have h := inverseSquareSeriesValue_bound
    (fun n => (pairedGlobalSecondDerivativeTailTerm z hz B n).val)
    (fun n => (pairedGlobalSecondDerivativeTailTerm z hz B n).property) 65536
    (pairedGlobalSecondDerivativeTailTerm_bound z hz B hB)
  exact h.mono (by decide +kernel)


theorem pairedDerivativeTailValue_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hB : Small z.val (B:Rat)) :
    Small (pairedDerivativeTailValue z hz B) 2048 := by
  have h := inverseSquareSeriesValue_bound
    (fun n => (pairedDerivativeTailTerm z hz B n).val)
    (fun n => (pairedDerivativeTailTerm z hz B n).property) 1024
    (pairedDerivativeTailTerm_bound z hz B hB)
  exact h.mono (by decide +kernel)

theorem pairedTailValue_bound (z : Scalar) (B : Nat) (hz : Small z.val (B:Rat)) :
    Small (pairedTailValue z B hz) (32*(B:Rat)) := by
  have h := inverseSquareSeriesValue_bound
    (fun n => (pairedTailTerm z B hz n).val)
    (fun n => (pairedTailTerm z B hz n).property) (16*B) (pairedTailTerm_bound z B hz)
  apply h.mono
  rw [Rat.natCast_mul,show ((16:Nat):Rat)=16 by decide +kernel]
  grind only

end ComputableAnalysis.ModularForms
