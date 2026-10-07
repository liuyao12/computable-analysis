import ComputableAnalysis.ModularForms.PairedDivisionDerivativeRemainderPrefixes

/-! Actual limits of the summable paired reciprocal remainders retain their quadratic bound. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedDivisionDerivativeRemainderTerm (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z) (n : Nat) : ComplexRaw :=
  (pairedDivisionDerivativeRemainder a z ha hz n).val

theorem pairedDivisionDerivativeRemainderTerm_valid (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z) (n : Nat) :
    (pairedDivisionDerivativeRemainderTerm a z ha hz n).Valid :=
  (pairedDivisionDerivativeRemainder a z ha hz n).property

def pairedDivisionDerivativeRemainderRate (H : Rat) (N : Nat) : Rat :=
  61440*(((N+1:Nat):Rat))⁻¹*H*H

theorem pairedDivisionDerivativeRemainderRate_shrinks (H : Rat) : ShrinksToZero (pairedDivisionDerivativeRemainderRate H) := by
  have hs : 0≤H*H := by
    by_cases h : 0≤H
    · exact Rat.mul_nonneg h h
    · have hn : 0≤ -H := by grind only
      have hm := Rat.mul_nonneg hn hn
      grind only
  have h := SeriesLimitLaws.shrinks_scale _ (pairedReciprocalTail_shrinks 61440) (H*H) hs
  have he : (fun n => (H*H)*(((61440:Nat):Rat)*(((n+1:Nat):Rat))⁻¹))=pairedDivisionDerivativeRemainderRate H := by
    funext n
    unfold pairedDivisionDerivativeRemainderRate
    rw [show ((61440:Nat):Rat)=61440 by decide +kernel]
    grind only
  exact he ▸ h

theorem pairedDivisionDerivativeRemainderPrefix_cauchy (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H)
    (N n : Nat) (hNn : N≤n) :
    Small (sub (ScalarSeries.block (pairedDivisionDerivativeRemainderTerm a z ha hz) 0 (n+1))
      (ScalarSeries.block (pairedDivisionDerivativeRemainderTerm a z ha hz) 0 (N+1)))
      (pairedDivisionDerivativeRemainderRate H N) := by
  have he := ScalarSeries.prefix_difference (pairedDivisionDerivativeRemainderTerm a z ha hz)
    (pairedDivisionDerivativeRemainderTerm_valid a z ha hz) (N+1) (n-N)
  rw [show N+1+(n-N)=n+1 by omega] at he
  exact Small.congr
    (ScalarSeries.block_valid _ (pairedDivisionDerivativeRemainderTerm_valid a z ha hz) (N+1) (n-N))
    (sub_valid (ScalarSeries.block_valid _ (pairedDivisionDerivativeRemainderTerm_valid a z ha hz) 0 (n+1))
      (ScalarSeries.block_valid _ (pairedDivisionDerivativeRemainderTerm_valid a z ha hz) 0 (N+1)))
    (equiv_symm he)
    (pairedDivisionDerivativeRemainder_block_tail (N+1) (n-N) (by omega) a z ha hz H hH hd)

def pairedDivisionDerivativeRemainderValue (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z) (H : Rat) : ComplexRaw :=
  RepresentedCauchySum.value (fun N => ScalarSeries.block (pairedDivisionDerivativeRemainderTerm a z ha hz) 0 (N+1))
    (fun N => ScalarSeries.block_valid _ (pairedDivisionDerivativeRemainderTerm_valid a z ha hz) 0 (N+1))
    (pairedDivisionDerivativeRemainderRate H)

theorem pairedDivisionDerivativeRemainderValue_valid (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    (pairedDivisionDerivativeRemainderValue a z ha hz H).Valid :=
  RepresentedCauchySum.value_valid _ _ _ (pairedDivisionDerivativeRemainderRate_shrinks H)
    (pairedDivisionDerivativeRemainderPrefix_cauchy a z ha hz H hH hd)

theorem pairedDivisionDerivativeRemainderValue_close (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (sub (pairedDivisionDerivativeRemainderValue a z ha hz H)
      (ScalarSeries.block (pairedDivisionDerivativeRemainderTerm a z ha hz) 0 (N+1)))
      (pairedDivisionDerivativeRemainderRate H N) :=
  RepresentedCauchySum.value_close_prefix _ _ _
    (pairedDivisionDerivativeRemainderPrefix_cauchy a z ha hz H hH hd) N

private theorem divisionDerivativeRemainder_squareBlock_split (k : Nat) :
    reciprocalSquareBlock 0 (k+1)=1+reciprocalSquareBlock 1 k := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    change reciprocalSquareBlock 0 (k+1)+reciprocalSquare (0+(k+1)+1)=
      1+(reciprocalSquareBlock 1 k+reciprocalSquare (1+k+1))
    rw [ih,show 0+(k+1)+1=1+k+1 by omega]
    grind only

private theorem divisionDerivativeRemainder_squareBlock_bound (k : Nat) : reciprocalSquareBlock 0 k≤2 := by
  cases k with
  | zero => change (0:Rat)≤2; decide +kernel
  | succ k =>
    rw [divisionDerivativeRemainder_squareBlock_split]
    have h := reciprocalSquareBlock_tail 1 k (by omega)
    rw [show ((1:Nat):Rat)⁻¹=1 by decide +kernel] at h
    grind only

theorem pairedDivisionDerivativeRemainderValue_bound (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (pairedDivisionDerivativeRemainderValue a z ha hz H) (122880*H*H) :=
  SeriesLimitLaws.small_of_prefix_bound _ (pairedDivisionDerivativeRemainderValue_valid a z ha hz H hH hd)
    _ (fun N => ScalarSeries.block_valid _ (pairedDivisionDerivativeRemainderTerm_valid a z ha hz) 0 (N+1))
    _ _ (pairedDivisionDerivativeRemainderRate_shrinks H)
    (pairedDivisionDerivativeRemainderValue_close a z ha hz H hH hd)
    (fun N => by
      apply (pairedDivisionDerivativeRemainder_block_bound 0 (N+1) a z ha hz H hH hd).mono
      have hb := Rat.mul_le_mul_of_nonneg_left (divisionDerivativeRemainder_squareBlock_bound (N+1))
        (Rat.mul_nonneg (Rat.mul_nonneg (show (0:Rat)≤61440 by decide) hH) hH)
      grind only)

end ComputableAnalysis.ModularForms
