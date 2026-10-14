import ComputableAnalysis.ModularForms.PairedOffPoleTailRemainderPrefixes
import ComputableAnalysis.ModularForms.InverseSquareSeriesBound

/-! Constructed limits and quadratic bounds for actual off-pole remainder sums. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedOffPoleTailRemainderCoefficient (B : Nat) : Rat :=
  1536*(B:Rat)+65536*(B:Rat)*(B:Rat)*(B:Rat)

theorem pairedOffPoleTailRemainderCoefficient_nonneg (B : Nat) :
    0≤pairedOffPoleTailRemainderCoefficient B := by
  have hB : (0:Rat)≤(B:Rat) := Rat.natCast_nonneg
  have h3 := Rat.mul_nonneg (Rat.mul_nonneg hB hB) hB
  unfold pairedOffPoleTailRemainderCoefficient
  grind only

def pairedOffPoleTailRemainderRate (B : Nat) (H : Rat) (N : Nat) : Rat :=
  pairedOffPoleTailRemainderCoefficient B*((N+1:Nat):Rat)⁻¹*H*H

theorem pairedOffPoleTailRemainderRate_shrinks (B : Nat) (H : Rat) :
    ShrinksToZero (pairedOffPoleTailRemainderRate B H) := by
  have hH2 : 0≤H*H := by
    by_cases h : 0≤H
    · exact Rat.mul_nonneg h h
    · have hn : 0≤ -H := by grind only
      have hh := Rat.mul_nonneg hn hn
      grind only
  have hs := SeriesLimitLaws.shrinks_scale _ (pairedReciprocalTail_shrinks 1)
    (pairedOffPoleTailRemainderCoefficient B*(H*H))
    (Rat.mul_nonneg (pairedOffPoleTailRemainderCoefficient_nonneg B) hH2)
  have he : (fun N => (pairedOffPoleTailRemainderCoefficient B*(H*H))*
      (((1:Nat):Rat)*((N+1:Nat):Rat)⁻¹))=pairedOffPoleTailRemainderRate B H := by
    funext N
    unfold pairedOffPoleTailRemainderRate
    rw [show ((1:Nat):Rat)=1 by decide +kernel]
    grind only
  exact he ▸ hs

def pairedOffPoleTailRemainderPrefix (B : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z) (N : Nat) : ComplexRaw :=
  ScalarSeries.block (fun n => (pairedOffPoleTailTermRemainder B n a z ha hz).val) 0 (N+1)

theorem pairedOffPoleTailRemainderPrefix_valid (B : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z) (N : Nat) :
    (pairedOffPoleTailRemainderPrefix B a z ha hz N).Valid :=
  ScalarSeries.block_valid _ (fun n => (pairedOffPoleTailTermRemainder B n a z ha hz).property) 0 (N+1)

theorem pairedOffPoleTailRemainderPrefix_cauchy (B : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (N n : Nat) (hNn : N≤n) :
    Small (sub (pairedOffPoleTailRemainderPrefix B a z ha hz n)
      (pairedOffPoleTailRemainderPrefix B a z ha hz N)) (pairedOffPoleTailRemainderRate B H N) := by
  have he := ScalarSeries.prefix_difference
    (fun n => (pairedOffPoleTailTermRemainder B n a z ha hz).val)
    (fun n => (pairedOffPoleTailTermRemainder B n a z ha hz).property) (N+1) (n-N)
  rw [show N+1+(n-N)=n+1 by omega] at he
  exact Small.congr
    (ScalarSeries.block_valid _ (fun n => (pairedOffPoleTailTermRemainder B n a z ha hz).property) (N+1) (n-N))
    (sub_valid (pairedOffPoleTailRemainderPrefix_valid B a z ha hz n)
      (pairedOffPoleTailRemainderPrefix_valid B a z ha hz N)) (equiv_symm he)
    (pairedOffPoleTailRemainder_block_tail B (N+1) (n-N) (by omega) a z ha hz H hH hd)

def pairedOffPoleTailRemainderValue (B : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z) (H : Rat) : ComplexRaw :=
  RepresentedCauchySum.value (pairedOffPoleTailRemainderPrefix B a z ha hz)
    (pairedOffPoleTailRemainderPrefix_valid B a z ha hz) (pairedOffPoleTailRemainderRate B H)

theorem pairedOffPoleTailRemainderValue_valid (B : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    (pairedOffPoleTailRemainderValue B a z ha hz H).Valid :=
  RepresentedCauchySum.value_valid _ _ _ (pairedOffPoleTailRemainderRate_shrinks B H)
    (pairedOffPoleTailRemainderPrefix_cauchy B a z ha hz H hH hd)

theorem pairedOffPoleTailRemainderValue_close (B : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (sub (pairedOffPoleTailRemainderValue B a z ha hz H)
      (pairedOffPoleTailRemainderPrefix B a z ha hz N)) (pairedOffPoleTailRemainderRate B H N) :=
  RepresentedCauchySum.value_close_prefix _ _ _
    (pairedOffPoleTailRemainderPrefix_cauchy B a z ha hz H hH hd) N

theorem pairedOffPoleTailRemainderValue_bound (B : Nat) (a z : Scalar)
    (ha : LocalODE.interior (B:Rat) a) (hz : LocalODE.interior (B:Rat) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (pairedOffPoleTailRemainderValue B a z ha hz H)
      (2*pairedOffPoleTailRemainderCoefficient B*H*H) := by
  apply SeriesLimitLaws.small_of_prefix_bound _ (pairedOffPoleTailRemainderValue_valid B a z ha hz H hH hd)
    _ (pairedOffPoleTailRemainderPrefix_valid B a z ha hz) _ _
    (pairedOffPoleTailRemainderRate_shrinks B H) (pairedOffPoleTailRemainderValue_close B a z ha hz H hH hd)
  intro N
  apply (pairedOffPoleTailRemainder_block_bound B 0 (N+1) a z ha hz H hH hd).mono
  have hm := Rat.mul_le_mul_of_nonneg_left (inverseSquareBlock_zero_bound (N+1))
    (Rat.mul_nonneg (Rat.mul_nonneg (pairedOffPoleTailRemainderCoefficient_nonneg B) hH) hH)
  unfold pairedOffPoleTailRemainderCoefficient at hm ⊢
  grind only

end ComputableAnalysis.ModularForms
