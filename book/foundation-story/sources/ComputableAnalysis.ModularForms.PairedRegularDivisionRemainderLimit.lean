import ComputableAnalysis.ModularForms.PairedRegularDivisionRemainderPrefixes

/-! Actual limits of the summable paired reciprocal remainders retain their quadratic bound. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedRegularDivisionRemainderTerm (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z) (n : Nat) : ComplexRaw :=
  (pairedRegularDivisionRemainder a z ha hz n).val

theorem pairedRegularDivisionRemainderTerm_valid (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z) (n : Nat) :
    (pairedRegularDivisionRemainderTerm a z ha hz n).Valid :=
  (pairedRegularDivisionRemainder a z ha hz n).property

def pairedRegularDivisionRemainderRate (H : Rat) (N : Nat) : Rat :=
  2304*(((N+1:Nat):Rat))⁻¹*H*H

theorem pairedRegularDivisionRemainderRate_shrinks (H : Rat) : ShrinksToZero (pairedRegularDivisionRemainderRate H) := by
  have hs : 0≤H*H := by
    by_cases h : 0≤H
    · exact Rat.mul_nonneg h h
    · have hn : 0≤ -H := by grind only
      have hm := Rat.mul_nonneg hn hn
      grind only
  have h := SeriesLimitLaws.shrinks_scale _ (pairedReciprocalTail_shrinks 2304) (H*H) hs
  have he : (fun n => (H*H)*(((2304:Nat):Rat)*(((n+1:Nat):Rat))⁻¹))=pairedRegularDivisionRemainderRate H := by
    funext n
    unfold pairedRegularDivisionRemainderRate
    rw [show ((2304:Nat):Rat)=2304 by decide +kernel]
    grind only
  exact he ▸ h

theorem pairedRegularDivisionRemainderPrefix_cauchy (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H)
    (N n : Nat) (hNn : N≤n) :
    Small (sub (ScalarSeries.block (pairedRegularDivisionRemainderTerm a z ha hz) 0 (n+1))
      (ScalarSeries.block (pairedRegularDivisionRemainderTerm a z ha hz) 0 (N+1)))
      (pairedRegularDivisionRemainderRate H N) := by
  have he := ScalarSeries.prefix_difference (pairedRegularDivisionRemainderTerm a z ha hz)
    (pairedRegularDivisionRemainderTerm_valid a z ha hz) (N+1) (n-N)
  rw [show N+1+(n-N)=n+1 by omega] at he
  exact Small.congr
    (ScalarSeries.block_valid _ (pairedRegularDivisionRemainderTerm_valid a z ha hz) (N+1) (n-N))
    (sub_valid (ScalarSeries.block_valid _ (pairedRegularDivisionRemainderTerm_valid a z ha hz) 0 (n+1))
      (ScalarSeries.block_valid _ (pairedRegularDivisionRemainderTerm_valid a z ha hz) 0 (N+1)))
    (equiv_symm he)
    (pairedRegularDivisionRemainder_block_tail (N+1) (n-N) (by omega) a z ha hz H hH hd)

def pairedRegularDivisionRemainderValue (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z) (H : Rat) : ComplexRaw :=
  RepresentedCauchySum.value (fun N => ScalarSeries.block (pairedRegularDivisionRemainderTerm a z ha hz) 0 (N+1))
    (fun N => ScalarSeries.block_valid _ (pairedRegularDivisionRemainderTerm_valid a z ha hz) 0 (N+1))
    (pairedRegularDivisionRemainderRate H)

theorem pairedRegularDivisionRemainderValue_valid (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    (pairedRegularDivisionRemainderValue a z ha hz H).Valid :=
  RepresentedCauchySum.value_valid _ _ _ (pairedRegularDivisionRemainderRate_shrinks H)
    (pairedRegularDivisionRemainderPrefix_cauchy a z ha hz H hH hd)

theorem pairedRegularDivisionRemainderValue_close (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (sub (pairedRegularDivisionRemainderValue a z ha hz H)
      (ScalarSeries.block (pairedRegularDivisionRemainderTerm a z ha hz) 0 (N+1)))
      (pairedRegularDivisionRemainderRate H N) :=
  RepresentedCauchySum.value_close_prefix _ _ _
    (pairedRegularDivisionRemainderPrefix_cauchy a z ha hz H hH hd) N

private theorem divisionRemainder_squareBlock_split (k : Nat) :
    reciprocalSquareBlock 0 (k+1)=1+reciprocalSquareBlock 1 k := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    change reciprocalSquareBlock 0 (k+1)+reciprocalSquare (0+(k+1)+1)=
      1+(reciprocalSquareBlock 1 k+reciprocalSquare (1+k+1))
    rw [ih,show 0+(k+1)+1=1+k+1 by omega]
    grind only

private theorem divisionRemainder_squareBlock_bound (k : Nat) : reciprocalSquareBlock 0 k≤2 := by
  cases k with
  | zero => change (0:Rat)≤2; decide +kernel
  | succ k =>
    rw [divisionRemainder_squareBlock_split]
    have h := reciprocalSquareBlock_tail 1 k (by omega)
    rw [show ((1:Nat):Rat)⁻¹=1 by decide +kernel] at h
    grind only

theorem pairedRegularDivisionRemainderValue_bound (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (pairedRegularDivisionRemainderValue a z ha hz H) (4608*H*H) :=
  SeriesLimitLaws.small_of_prefix_bound _ (pairedRegularDivisionRemainderValue_valid a z ha hz H hH hd)
    _ (fun N => ScalarSeries.block_valid _ (pairedRegularDivisionRemainderTerm_valid a z ha hz) 0 (N+1))
    _ _ (pairedRegularDivisionRemainderRate_shrinks H)
    (pairedRegularDivisionRemainderValue_close a z ha hz H hH hd)
    (fun N => by
      apply (pairedRegularDivisionRemainder_block_bound 0 (N+1) a z ha hz H hH hd).mono
      have hb := Rat.mul_le_mul_of_nonneg_left (divisionRemainder_squareBlock_bound (N+1))
        (Rat.mul_nonneg (Rat.mul_nonneg (show (0:Rat)≤2304 by decide) hH) hH)
      grind only)

end ComputableAnalysis.ModularForms
