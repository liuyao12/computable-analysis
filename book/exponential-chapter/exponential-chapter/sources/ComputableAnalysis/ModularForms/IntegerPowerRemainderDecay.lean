import ComputableAnalysis.ModularForms.IntegerPowerRemainderBounds
import ComputableAnalysis.ModularForms.InverseSquareSeriesBound

/-! Summable inverse-square decay of actual integer-power remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private theorem quadratic_scaled_mono (c x y H : Rat)
    (hc : 0≤c) (hH : 0≤H) (hxy : x≤y) :
    2*(c*x)*H*H≤2*c*y*H*H := by
  have h := Rat.mul_le_mul_of_nonneg_left hxy (Rat.mul_nonneg (by decide : (0:Rat)≤2) hc)
  have hh := Rat.mul_le_mul_of_nonneg_right (Rat.mul_le_mul_of_nonneg_right h hH) hH
  grind only

theorem pairedIntegerPowerMap_remainder_large (k n : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (R H : Rat) (hR : 0≤R) (hH : 0≤H)
    (hA : Small a.val R) (hZ : Small z.val R)
    (hlarge : 16*R*R≤pairedIntegerSquare (n+1)) (hRn : R≤((n+1:Nat):Rat))
    (hd : Small (sub z.val a.val) H) :
    Small (DomainFunctions.remainder (pairedIntegerPowerMap k n) a ha
      ((pairedIntegerPowerMap_holomorphic k n).derivative a ha) z hz)
      (2*powerRemainderCoefficient 16 k*reciprocalSquare (n+1)*H*H) := by
  have hm : 0≤16*(1/((n+1:Nat):Rat)) := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.mul_nonneg (by decide) (Rat.le_of_lt (Rat.inv_pos.mpr (by
      exact_mod_cast (show 0<n+1 by omega))))
  have hb := pairedIntegerPowerMap_remainder_bound k n a z ha hz _ H hm hH
    (upperIntegerReciprocal_minus_bound a ha R hR hA (n+1) (by omega) hlarge hRn)
    (upperIntegerReciprocal_plus_bound a ha R hR hA (n+1) (by omega) hlarge hRn)
    (upperIntegerReciprocal_minus_bound z hz R hR hZ (n+1) (by omega) hlarge hRn)
    (upperIntegerReciprocal_plus_bound z hz R hR hZ (n+1) (by omega) hlarge hRn) hd
  rw [Rat.div_def,Rat.one_mul,powerRemainderCoefficient_scale] at hb
  exact hb.mono (quadratic_scaled_mono _ _ _ H
    (powerRemainderCoefficient_nonnegative 16 (by decide) k) hH
    (reciprocal_integer_power_le_square (n+1) (k+2) (by omega) (by omega)))

def pairedIntegerPowerTailRemainder (k B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) (n : Nat) : ComplexRaw :=
  DomainFunctions.remainder (pairedIntegerPowerMap k (4*B+n)) a ha
    ((pairedIntegerPowerMap_holomorphic k (4*B+n)).derivative a ha) z hz

theorem pairedIntegerPowerTailRemainder_valid (k B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) (n : Nat) :
    (pairedIntegerPowerTailRemainder k B a z ha hz n).Valid := DomainFunctions.remainder_valid _ _ _ _ _ _

theorem pairedIntegerPowerTailRemainder_bound (k B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (n : Nat) :
    Small (pairedIntegerPowerTailRemainder k B a z ha hz n)
      ((2*powerRemainderCoefficient 16 k*H*H)*reciprocalSquare (n+1)) := by
  have hb := pairedIntegerPowerMap_remainder_large k (4*B+n) a z ha hz (B:Rat) H
    Rat.natCast_nonneg hH hA hZ (pairedTailShift_large B n)
    (by exact_mod_cast (show B≤4*B+n+1 by omega)) hd
  have hc : 0≤2*powerRemainderCoefficient 16 k*H*H :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide)
      (powerRemainderCoefficient_nonnegative 16 (by decide) k)) hH) hH
  have hm := Rat.mul_le_mul_of_nonneg_left
    (pairedDerivative_reciprocalSquare_antitone (n+1) (4*B+n+1) (by omega) (by omega)) hc
  apply hb.mono
  have algebra (c x y H : Rat) (h : (2*c*H*H)*x≤(2*c*H*H)*y) :
      2*c*x*H*H≤(2*c*H*H)*y := by grind only
  exact algebra _ _ _ _ hm

private theorem rational_distribute (C x y : Rat) : C*x+C*y=C*(x+y) := by grind only

theorem inverseSquare_block_bound_rat (t : Nat → ComplexRaw) (C : Rat)
    (hB : ∀ n, Small (t n) (C*reciprocalSquare (n+1))) (M N : Nat) :
    Small (ScalarSeries.block t M N) (C*reciprocalSquareBlock M N) := by
  induction N with
  | zero =>
    change Small ComplexRaw.zero (C*0)
    rw [Rat.mul_zero]
    exact Small.zero (by decide)
  | succ N ih =>
    have h := LocalODE.small_add ih (hB (M+N))
    rw [rational_distribute] at h
    exact h

theorem pairedIntegerPowerTailRemainder_prefix_bound (k B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (ScalarSeries.block (pairedIntegerPowerTailRemainder k B a z ha hz) 0 N)
      (4*powerRemainderCoefficient 16 k*H*H) := by
  let C := 2*powerRemainderCoefficient 16 k*H*H
  have hc : 0≤C := Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide)
    (powerRemainderCoefficient_nonnegative 16 (by decide) k)) hH) hH
  have hb := inverseSquare_block_bound_rat _ C
    (pairedIntegerPowerTailRemainder_bound k B a z ha hz hA hZ H hH hd) 0 N
  have hm := Rat.mul_le_mul_of_nonneg_left (inverseSquareBlock_zero_bound N) hc
  have he (c H : Rat) : (2*c*H*H)*2=4*c*H*H := by grind only
  rw [show C*2=4*powerRemainderCoefficient 16 k*H*H from he _ _] at hm
  exact hb.mono hm

end ComputableAnalysis.ModularForms
