import ComputableAnalysis.ModularForms.PairedHorizontalDerivativeBlocks
import ComputableAnalysis.ModularForms.PairedTailSeries

/-! Uniform bounds retaining the actual starting index of the paired value tail. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedTailTerm_shifted_bound (z : Scalar) (B : Nat) (hz : Small z.val (B:Rat)) (n : Nat) :
    Small (pairedTailTerm z B hz n).val ((16*(B:Rat))*reciprocalSquare (4*B+n+1)) := by
  let k := pairedTailShift B n
  have hk : 0<k := by unfold k pairedTailShift; omega
  simpa only [pairedTailTerm,pairedTailShift,pairedIntegerSquare,reciprocalSquare,k,
    Rat.div_def,Rat.one_mul] using pairedIntegerQuotient_bound z (B:Rat) k Rat.natCast_nonneg hz hk
    (pairedTailShift_large B n)
    (pairedIntegerDenominator_nonzero z (B:Rat) k Rat.natCast_nonneg hz hk (pairedTailShift_large B n))

theorem pairedTailTerm_block_shifted_bound (z : Scalar) (B : Nat)
    (hz : Small z.val (B:Rat)) (K : Nat) :
    Small (ScalarSeries.block (fun n => (pairedTailTerm z B hz n).val) 0 K)
      (16*(B:Rat)*reciprocalSquareBlock (4*B) K) := by
  induction K with
  | zero => exact Small.zero (by change (0:Rat)≤16*(B:Rat)*0; simp [Rat.mul_zero])
  | succ K ih =>
    have hs := LocalODE.small_add ih (pairedTailTerm_shifted_bound z B hz K)
    have he : 16*(B:Rat)*reciprocalSquareBlock (4*B) K+
        16*(B:Rat)*reciprocalSquare (4*B+K+1)=16*(B:Rat)*reciprocalSquareBlock (4*B) (K+1) := by
      rw [reciprocalSquareBlock]; grind only
    rw [he] at hs
    simpa only [ScalarSeries.block,Nat.zero_add] using hs

theorem pairedTailValue_uniform_bound (z : Scalar) (B : Nat)
    (hz : Small z.val (B:Rat)) (hB : 0<B) : Small (pairedTailValue z B hz) 4 := by
  apply SeriesLimitLaws.small_of_prefix_bound _ (pairedTailValue_valid z B hz)
    (fun N => ScalarSeries.block (fun n => (pairedTailTerm z B hz n).val) 0 (N+1))
    (fun N => ScalarSeries.block_valid _ (fun n => (pairedTailTerm z B hz n).property) 0 (N+1))
    4 (fun N => ((16*B:Nat):Rat)*((N+1:Nat):Rat)⁻¹)
    (pairedReciprocalTail_shrinks (16*B)) (pairedTailValue_close z B hz)
  intro N
  apply (pairedTailTerm_block_shifted_bound z B hz (N+1)).mono
  have ht := Rat.mul_le_mul_of_nonneg_left (reciprocalSquareBlock_tail (4*B) (N+1) (by omega))
    (Rat.mul_nonneg (show (0:Rat)≤16 by decide +kernel) (show (0:Rat)≤(B:Rat) from Rat.natCast_nonneg))
  have hpos : (0:Rat)<((4*B:Nat):Rat) := by exact_mod_cast (show 0<4*B by omega)
  have hc := Rat.mul_inv_cancel ((4*B:Nat):Rat) (Rat.ne_of_gt hpos)
  simp only [Rat.natCast_mul,show ((4:Nat):Rat)=4 by decide +kernel] at ht hc
  grind only

end ComputableAnalysis.ModularForms
