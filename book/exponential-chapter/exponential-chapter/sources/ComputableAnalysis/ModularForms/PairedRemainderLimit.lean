import ComputableAnalysis.ModularForms.PairedTermRemainder

/-! Actual limits of the summable paired reciprocal remainders retain their quadratic bound. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedTailRemainderTerm (B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) (n : Nat) : ComplexRaw :=
  DomainFunctions.remainder (pairedReciprocalTermMap (4*B+n)) a ha
    (upperPairedReciprocalDerivative a ha (pairedTailShift B n)) z hz

theorem pairedTailRemainderTerm_valid (B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) (n : Nat) :
    (pairedTailRemainderTerm B a z ha hz n).Valid := DomainFunctions.remainder_valid _ _ _ _ _ _

def pairedTailRemainderRate (H : Rat) (N : Nat) : Rat :=
  524288*(((N+1:Nat):Rat))⁻¹*H*H

theorem pairedTailRemainderRate_shrinks (H : Rat) : ShrinksToZero (pairedTailRemainderRate H) := by
  have hs : 0≤H*H := by
    by_cases h : 0≤H
    · exact Rat.mul_nonneg h h
    · have hn : 0≤ -H := by grind only
      have hm := Rat.mul_nonneg hn hn
      grind only
  have h := SeriesLimitLaws.shrinks_scale _ (pairedReciprocalTail_shrinks 524288) (H*H) hs
  have he : (fun n => (H*H)*(((524288:Nat):Rat)*(((n+1:Nat):Rat))⁻¹))=pairedTailRemainderRate H := by
    funext n
    unfold pairedTailRemainderRate
    rw [show ((524288:Nat):Rat)=524288 by decide +kernel]
    grind only
  exact he ▸ h

theorem pairedTailRemainderPrefix_cauchy (B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H)
    (N n : Nat) (hNn : N≤n) :
    Small (sub (ScalarSeries.block (pairedTailRemainderTerm B a z ha hz) 0 (n+1))
      (ScalarSeries.block (pairedTailRemainderTerm B a z ha hz) 0 (N+1)))
      (pairedTailRemainderRate H N) := by
  have he := ScalarSeries.prefix_difference (pairedTailRemainderTerm B a z ha hz)
    (pairedTailRemainderTerm_valid B a z ha hz) (N+1) (n-N)
  rw [show N+1+(n-N)=n+1 by omega] at he
  exact Small.congr
    (ScalarSeries.block_valid _ (pairedTailRemainderTerm_valid B a z ha hz) (N+1) (n-N))
    (sub_valid (ScalarSeries.block_valid _ (pairedTailRemainderTerm_valid B a z ha hz) 0 (n+1))
      (ScalarSeries.block_valid _ (pairedTailRemainderTerm_valid B a z ha hz) 0 (N+1)))
    (equiv_symm he)
    (pairedReciprocalTail_remainder_block_tail B (N+1) (n-N) (by omega) a z ha hz hA hZ H hH hd)

def pairedTailRemainderValue (B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) (H : Rat) : ComplexRaw :=
  RepresentedCauchySum.value (fun N => ScalarSeries.block (pairedTailRemainderTerm B a z ha hz) 0 (N+1))
    (fun N => ScalarSeries.block_valid _ (pairedTailRemainderTerm_valid B a z ha hz) 0 (N+1))
    (pairedTailRemainderRate H)

theorem pairedTailRemainderValue_valid (B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    (pairedTailRemainderValue B a z ha hz H).Valid :=
  RepresentedCauchySum.value_valid _ _ _ (pairedTailRemainderRate_shrinks H)
    (pairedTailRemainderPrefix_cauchy B a z ha hz hA hZ H hH hd)

theorem pairedTailRemainderValue_close (B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (sub (pairedTailRemainderValue B a z ha hz H)
      (ScalarSeries.block (pairedTailRemainderTerm B a z ha hz) 0 (N+1)))
      (pairedTailRemainderRate H N) :=
  RepresentedCauchySum.value_close_prefix _ _ _
    (pairedTailRemainderPrefix_cauchy B a z ha hz hA hZ H hH hd) N

theorem pairedTailRemainderValue_bound (B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (pairedTailRemainderValue B a z ha hz H) (1048576*H*H) :=
  SeriesLimitLaws.small_of_prefix_bound _ (pairedTailRemainderValue_valid B a z ha hz hA hZ H hH hd)
    _ (fun N => ScalarSeries.block_valid _ (pairedTailRemainderTerm_valid B a z ha hz) 0 (N+1))
    _ _ (pairedTailRemainderRate_shrinks H)
    (pairedTailRemainderValue_close B a z ha hz hA hZ H hH hd)
    (fun N => pairedReciprocalTail_remainder_prefix_bound B (N+1) a z ha hz hA hZ H hH hd)

end ComputableAnalysis.ModularForms
