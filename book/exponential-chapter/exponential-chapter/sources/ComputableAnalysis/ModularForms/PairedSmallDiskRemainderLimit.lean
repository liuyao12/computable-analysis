import ComputableAnalysis.ModularForms.PairedSmallDiskRemainder

/-! Actual limits of the summable paired reciprocal remainders retain their quadratic bound. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedSmallDiskRemainderTerm (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z) (n : Nat) : ComplexRaw :=
  DomainFunctions.remainder (pairedSmallDiskTermMap n) a ha
    (pairedSmallDiskDerivativeTerm a (LocalODE.interior_bound _ a ha) n) z hz

theorem pairedSmallDiskRemainderTerm_valid (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z) (n : Nat) :
    (pairedSmallDiskRemainderTerm a z ha hz n).Valid := DomainFunctions.remainder_valid _ _ _ _ _ _

def pairedSmallDiskRemainderRate (H : Rat) (N : Nat) : Rat :=
  131072*(((N+1:Nat):Rat))⁻¹*H*H

theorem pairedSmallDiskRemainderRate_shrinks (H : Rat) : ShrinksToZero (pairedSmallDiskRemainderRate H) := by
  have hs : 0≤H*H := by
    by_cases h : 0≤H
    · exact Rat.mul_nonneg h h
    · have hn : 0≤ -H := by grind only
      have hm := Rat.mul_nonneg hn hn
      grind only
  have h := SeriesLimitLaws.shrinks_scale _ (pairedReciprocalTail_shrinks 131072) (H*H) hs
  have he : (fun n => (H*H)*(((131072:Nat):Rat)*(((n+1:Nat):Rat))⁻¹))=pairedSmallDiskRemainderRate H := by
    funext n
    unfold pairedSmallDiskRemainderRate
    rw [show ((131072:Nat):Rat)=131072 by decide +kernel]
    grind only
  exact he ▸ h

theorem pairedSmallDiskRemainderPrefix_cauchy (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H)
    (N n : Nat) (hNn : N≤n) :
    Small (sub (ScalarSeries.block (pairedSmallDiskRemainderTerm a z ha hz) 0 (n+1))
      (ScalarSeries.block (pairedSmallDiskRemainderTerm a z ha hz) 0 (N+1)))
      (pairedSmallDiskRemainderRate H N) := by
  have he := ScalarSeries.prefix_difference (pairedSmallDiskRemainderTerm a z ha hz)
    (pairedSmallDiskRemainderTerm_valid a z ha hz) (N+1) (n-N)
  rw [show N+1+(n-N)=n+1 by omega] at he
  exact Small.congr
    (ScalarSeries.block_valid _ (pairedSmallDiskRemainderTerm_valid a z ha hz) (N+1) (n-N))
    (sub_valid (ScalarSeries.block_valid _ (pairedSmallDiskRemainderTerm_valid a z ha hz) 0 (n+1))
      (ScalarSeries.block_valid _ (pairedSmallDiskRemainderTerm_valid a z ha hz) 0 (N+1)))
    (equiv_symm he)
    (pairedSmallDiskRemainder_block_tail (N+1) (n-N) (by omega) a z ha hz H hH hd)

def pairedSmallDiskRemainderValue (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z) (H : Rat) : ComplexRaw :=
  RepresentedCauchySum.value (fun N => ScalarSeries.block (pairedSmallDiskRemainderTerm a z ha hz) 0 (N+1))
    (fun N => ScalarSeries.block_valid _ (pairedSmallDiskRemainderTerm_valid a z ha hz) 0 (N+1))
    (pairedSmallDiskRemainderRate H)

theorem pairedSmallDiskRemainderValue_valid (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    (pairedSmallDiskRemainderValue a z ha hz H).Valid :=
  RepresentedCauchySum.value_valid _ _ _ (pairedSmallDiskRemainderRate_shrinks H)
    (pairedSmallDiskRemainderPrefix_cauchy a z ha hz H hH hd)

theorem pairedSmallDiskRemainderValue_close (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (sub (pairedSmallDiskRemainderValue a z ha hz H)
      (ScalarSeries.block (pairedSmallDiskRemainderTerm a z ha hz) 0 (N+1)))
      (pairedSmallDiskRemainderRate H N) :=
  RepresentedCauchySum.value_close_prefix _ _ _
    (pairedSmallDiskRemainderPrefix_cauchy a z ha hz H hH hd) N

theorem pairedSmallDiskRemainderValue_bound (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (pairedSmallDiskRemainderValue a z ha hz H) (262144*H*H) :=
  SeriesLimitLaws.small_of_prefix_bound _ (pairedSmallDiskRemainderValue_valid a z ha hz H hH hd)
    _ (fun N => ScalarSeries.block_valid _ (pairedSmallDiskRemainderTerm_valid a z ha hz) 0 (N+1))
    _ _ (pairedSmallDiskRemainderRate_shrinks H)
    (pairedSmallDiskRemainderValue_close a z ha hz H hH hd)
    (fun N => pairedSmallDiskRemainder_prefix_bound (N+1) a z ha hz H hH hd)

end ComputableAnalysis.ModularForms
