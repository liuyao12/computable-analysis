import ComputableAnalysis.ModularForms.IntegerPowerRemainderDecay

/-! Constructed convergent tails of actual reciprocal-power remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem rationalInverseSquareRate_shrinks (C : Rat) (hC : 0≤C) :
    ShrinksToZero (fun n => C*(((n+1:Nat):Rat))⁻¹) := by
  have h : ShrinksToZero (fun n => (((n+1:Nat):Rat))⁻¹) := by
    simpa only [show ((1:Nat):Rat)=1 by decide +kernel,Rat.one_mul] using pairedReciprocalTail_shrinks 1
  exact SeriesLimitLaws.shrinks_scale _ h C hC

theorem rationalInverseSquare_prefix_cauchy (t : Nat → ComplexRaw)
    (ht : ∀ n, (t n).Valid) (C : Rat) (hC : 0≤C)
    (hB : ∀ n, Small (t n) (C*reciprocalSquare (n+1))) (N n : Nat) (hNn : N≤n) :
    Small (sub (ScalarSeries.block t 0 (n+1)) (ScalarSeries.block t 0 (N+1)))
      (C*(((N+1:Nat):Rat))⁻¹) := by
  have he := ScalarSeries.prefix_difference t ht (N+1) (n-N)
  rw [show N+1+(n-N)=n+1 by omega] at he
  have hb := (inverseSquare_block_bound_rat t C hB (N+1) (n-N)).mono
    (Rat.mul_le_mul_of_nonneg_left (reciprocalSquareBlock_tail (N+1) (n-N) (by omega)) hC)
  exact Small.congr (ScalarSeries.block_valid t ht (N+1) (n-N))
    (sub_valid (ScalarSeries.block_valid t ht 0 (n+1)) (ScalarSeries.block_valid t ht 0 (N+1)))
    (equiv_symm he) hb

def pairedIntegerPowerRemainderTailValue (k B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) (H : Rat) : ComplexRaw :=
  RepresentedCauchySum.value
    (fun N => ScalarSeries.block (pairedIntegerPowerTailRemainder k B a z ha hz) 0 (N+1))
    (fun N => ScalarSeries.block_valid _ (pairedIntegerPowerTailRemainder_valid k B a z ha hz) 0 (N+1))
    (fun N => (2*powerRemainderCoefficient 16 k*H*H)*(((N+1:Nat):Rat))⁻¹)

private theorem remainderConstant_nonneg (k : Nat) (H : Rat) (hH : 0≤H) :
    0≤2*powerRemainderCoefficient 16 k*H*H :=
  Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide)
    (powerRemainderCoefficient_nonnegative 16 (by decide) k)) hH) hH

theorem pairedIntegerPowerRemainderTailValue_valid (k B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    (pairedIntegerPowerRemainderTailValue k B a z ha hz H).Valid :=
  RepresentedCauchySum.value_valid _ _ _
    (rationalInverseSquareRate_shrinks _ (remainderConstant_nonneg k H hH))
    (rationalInverseSquare_prefix_cauchy _ (pairedIntegerPowerTailRemainder_valid k B a z ha hz) _
      (remainderConstant_nonneg k H hH) (pairedIntegerPowerTailRemainder_bound k B a z ha hz hA hZ H hH hd))

theorem pairedIntegerPowerRemainderTailValue_close (k B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (sub (pairedIntegerPowerRemainderTailValue k B a z ha hz H)
      (ScalarSeries.block (pairedIntegerPowerTailRemainder k B a z ha hz) 0 (N+1)))
      ((2*powerRemainderCoefficient 16 k*H*H)*(((N+1:Nat):Rat))⁻¹) :=
  RepresentedCauchySum.value_close_prefix _ _ _
    (rationalInverseSquare_prefix_cauchy _ (pairedIntegerPowerTailRemainder_valid k B a z ha hz) _
      (remainderConstant_nonneg k H hH) (pairedIntegerPowerTailRemainder_bound k B a z ha hz hA hZ H hH hd)) N

theorem pairedIntegerPowerRemainderTailValue_bound (k B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (pairedIntegerPowerRemainderTailValue k B a z ha hz H)
      (4*powerRemainderCoefficient 16 k*H*H) :=
  SeriesLimitLaws.small_of_prefix_bound _
    (pairedIntegerPowerRemainderTailValue_valid k B a z ha hz hA hZ H hH hd)
    (fun N => ScalarSeries.block (pairedIntegerPowerTailRemainder k B a z ha hz) 0 (N+1))
    (fun N => ScalarSeries.block_valid _ (pairedIntegerPowerTailRemainder_valid k B a z ha hz) 0 (N+1))
    _ _ (rationalInverseSquareRate_shrinks _ (remainderConstant_nonneg k H hH))
    (pairedIntegerPowerRemainderTailValue_close k B a z ha hz hA hZ H hH hd)
    (fun N => pairedIntegerPowerTailRemainder_prefix_bound k B a z ha hz hA hZ H hH hd (N+1))

end ComputableAnalysis.ModularForms
