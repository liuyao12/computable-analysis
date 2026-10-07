import ComputableAnalysis.ModularForms.PairedGlobalDerivativeRemainderTailBound

/-! Actual limits of the summable paired reciprocal remainders retain their quadratic bound. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedGlobalRemainderTailTerm (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) (B n : Nat) : ComplexRaw :=
  (pairedGlobalDerivativeRemainderTailTerm a z ha hz B n).val

theorem pairedGlobalRemainderTailTerm_valid (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) (B n : Nat) :
    (pairedGlobalRemainderTailTerm a z ha hz B n).Valid :=
  (pairedGlobalDerivativeRemainderTailTerm a z ha hz B n).property

def pairedGlobalRemainderTailRate (H : Rat) (N : Nat) : Rat :=
  12582912*(((N+1:Nat):Rat))⁻¹*H*H

theorem pairedGlobalRemainderTailRate_shrinks (H : Rat) : ShrinksToZero (pairedGlobalRemainderTailRate H) := by
  have hs : 0≤H*H := by
    by_cases h : 0≤H
    · exact Rat.mul_nonneg h h
    · have hn : 0≤ -H := by grind only
      have hm := Rat.mul_nonneg hn hn
      grind only
  have h := SeriesLimitLaws.shrinks_scale _ (pairedReciprocalTail_shrinks 12582912) (H*H) hs
  have he : (fun n => (H*H)*(((12582912:Nat):Rat)*(((n+1:Nat):Rat))⁻¹))=pairedGlobalRemainderTailRate H := by
    funext n
    unfold pairedGlobalRemainderTailRate
    rw [show ((12582912:Nat):Rat)=12582912 by decide +kernel]
    grind only
  exact he ▸ h

theorem pairedGlobalRemainderTailPrefix_cauchy (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hBa : Small a.val (B:Rat)) (hBz : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H)
    (N n : Nat) (hNn : N≤n) :
    Small (sub (ScalarSeries.block (pairedGlobalRemainderTailTerm a z ha hz B) 0 (n+1))
      (ScalarSeries.block (pairedGlobalRemainderTailTerm a z ha hz B) 0 (N+1)))
      (pairedGlobalRemainderTailRate H N) := by
  have he := ScalarSeries.prefix_difference (pairedGlobalRemainderTailTerm a z ha hz B)
    (pairedGlobalRemainderTailTerm_valid a z ha hz B) (N+1) (n-N)
  rw [show N+1+(n-N)=n+1 by omega] at he
  exact Small.congr
    (ScalarSeries.block_valid _ (pairedGlobalRemainderTailTerm_valid a z ha hz B) (N+1) (n-N))
    (sub_valid (ScalarSeries.block_valid _ (pairedGlobalRemainderTailTerm_valid a z ha hz B) 0 (n+1))
      (ScalarSeries.block_valid _ (pairedGlobalRemainderTailTerm_valid a z ha hz B) 0 (N+1)))
    (equiv_symm he)
    (pairedGlobalDerivativeRemainderTail_block_tail (N+1) (n-N) (by omega) a z ha hz B hBa hBz H hH hd)

def pairedGlobalRemainderTailValue (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) (B : Nat) (H : Rat) : ComplexRaw :=
  RepresentedCauchySum.value (fun N => ScalarSeries.block (pairedGlobalRemainderTailTerm a z ha hz B) 0 (N+1))
    (fun N => ScalarSeries.block_valid _ (pairedGlobalRemainderTailTerm_valid a z ha hz B) 0 (N+1))
    (pairedGlobalRemainderTailRate H)

theorem pairedGlobalRemainderTailValue_valid (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hBa : Small a.val (B:Rat)) (hBz : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    (pairedGlobalRemainderTailValue a z ha hz B H).Valid :=
  RepresentedCauchySum.value_valid _ _ _ (pairedGlobalRemainderTailRate_shrinks H)
    (pairedGlobalRemainderTailPrefix_cauchy a z ha hz B hBa hBz H hH hd)

theorem pairedGlobalRemainderTailValue_close (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hBa : Small a.val (B:Rat)) (hBz : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (sub (pairedGlobalRemainderTailValue a z ha hz B H)
      (ScalarSeries.block (pairedGlobalRemainderTailTerm a z ha hz B) 0 (N+1)))
      (pairedGlobalRemainderTailRate H N) :=
  RepresentedCauchySum.value_close_prefix _ _ _
    (pairedGlobalRemainderTailPrefix_cauchy a z ha hz B hBa hBz H hH hd) N

private theorem globalRemainderTail_squareBlock_split (k : Nat) :
    reciprocalSquareBlock 0 (k+1)=1+reciprocalSquareBlock 1 k := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    change reciprocalSquareBlock 0 (k+1)+reciprocalSquare (0+(k+1)+1)=
      1+(reciprocalSquareBlock 1 k+reciprocalSquare (1+k+1))
    rw [ih,show 0+(k+1)+1=1+k+1 by omega]
    grind only

private theorem globalRemainderTail_squareBlock_bound (k : Nat) : reciprocalSquareBlock 0 k≤2 := by
  cases k with
  | zero => change (0:Rat)≤2; decide +kernel
  | succ k =>
    rw [globalRemainderTail_squareBlock_split]
    have h := reciprocalSquareBlock_tail 1 k (by omega)
    rw [show ((1:Nat):Rat)⁻¹=1 by decide +kernel] at h
    grind only

theorem pairedGlobalRemainderTailValue_bound (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hBa : Small a.val (B:Rat)) (hBz : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (pairedGlobalRemainderTailValue a z ha hz B H) (25165824*H*H) :=
  SeriesLimitLaws.small_of_prefix_bound _ (pairedGlobalRemainderTailValue_valid a z ha hz B hBa hBz H hH hd)
    _ (fun N => ScalarSeries.block_valid _ (pairedGlobalRemainderTailTerm_valid a z ha hz B) 0 (N+1))
    _ _ (pairedGlobalRemainderTailRate_shrinks H)
    (pairedGlobalRemainderTailValue_close a z ha hz B hBa hBz H hH hd)
    (fun N => by
      apply (pairedGlobalDerivativeRemainderTail_block_bound 0 (N+1) a z ha hz B hBa hBz H hH hd).mono
      have hb := Rat.mul_le_mul_of_nonneg_left (globalRemainderTail_squareBlock_bound (N+1))
        (Rat.mul_nonneg (Rat.mul_nonneg (show (0:Rat)≤12582912 by decide) hH) hH)
      grind only)

end ComputableAnalysis.ModularForms
