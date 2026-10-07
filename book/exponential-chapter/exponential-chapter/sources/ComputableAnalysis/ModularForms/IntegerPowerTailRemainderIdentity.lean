import ComputableAnalysis.ModularForms.IntegerPowerDerivativeTail
import ComputableAnalysis.ModularForms.FiniteRemainderSum

/-! Identification of constructed power remainder tails with actual tail remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def integerPowerMapTailPrefix (z : Scalar) (hz : InUpperHalfPlane z.val) (k B N : Nat) : ComplexRaw :=
  ScalarSeries.block (fun n => ((pairedIntegerPowerMap k (4*B+n)).eval z hz).val) 0 N

theorem integerPowerMapTailPrefix_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (k B N : Nat) :
    (integerPowerMapTailPrefix z hz k B N).Valid :=
  ScalarSeries.block_valid _ (fun n => ((pairedIntegerPowerMap k (4*B+n)).eval z hz).property) 0 N

theorem integerPowerMapTailPrefix_close (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k B : Nat) (hk : 2≤k) (hB : Small z.val (B:Rat)) (N : Nat) :
    Small (sub (pairedIntegerPowerTailValue z hz k B) (integerPowerMapTailPrefix z hz k B (N+1)))
      (((2*32^k:Nat):Rat)*(((N+1:Nat):Rat))⁻¹) :=
  pairedIntegerPowerTailValue_close z hz k B hk hB N

theorem integerPowerTailRemainderPrefix_identity (k B N : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) :
    (ScalarSeries.block (pairedIntegerPowerTailRemainder k B a z ha hz) 0 N).Equiv
      (SeriesLimitLaws.remainder (integerPowerMapTailPrefix z hz k B N)
        (integerPowerMapTailPrefix a ha k B N) (integerPowerDerivativeTailPrefix a ha k B N)
        (sub z.val a.val)) :=
  finiteRemainderSum _ _ _
    (fun n => ((pairedIntegerPowerMap k (4*B+n)).eval z hz).property)
    (fun n => ((pairedIntegerPowerMap k (4*B+n)).eval a ha).property)
    (fun n => ((pairedIntegerPowerMap_holomorphic k (4*B+n)).derivative a ha).property)
    _ (sub_valid z.property a.property) 0 N

private theorem add_nonneg_mono (x y : Rat) (hy : 0≤y) : x≤x+y := by grind only
private theorem remainder_error_mono (e d r H : Rat) (hr : 0≤r) :
    e+e+2*d*H≤r+(e+e+(2*H)*d) := by grind only

theorem integerPowerTailRemainder_identity (k B : Nat) (hk : 2≤k) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    (pairedIntegerPowerRemainderTailValue k B a z ha hz H).Equiv
      (SeriesLimitLaws.remainder (pairedIntegerPowerTailValue z hz k B)
        (pairedIntegerPowerTailValue a ha k B) (integerPowerDerivativeTailValue a ha k B)
        (sub z.val a.val)) := by
  let e := fun N => ((2*32^k:Nat):Rat)*(((N+1:Nat):Rat))⁻¹
  let d := fun N => (k:Rat)*(((2*32^(k+1):Nat):Rat)*(((N+1:Nat):Rat))⁻¹)
  let r := fun N => (2*powerRemainderCoefficient 16 k*H*H)*(((N+1:Nat):Rat))⁻¹
  have he : ShrinksToZero e := pairedReciprocalTail_shrinks (2*32^k)
  have hdRate : ShrinksToZero d := SeriesLimitLaws.shrinks_scale _
    (pairedReciprocalTail_shrinks (2*32^(k+1))) (k:Rat) Rat.natCast_nonneg
  have hc : 0≤2*powerRemainderCoefficient 16 k*H*H :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide)
      (powerRemainderCoefficient_nonnegative 16 (by decide) k)) hH) hH
  have hr : ShrinksToZero r := rationalInverseSquareRate_shrinks _ hc
  let s := fun N => e N+e N+(2*H)*d N
  have hs : ShrinksToZero s := RepresentedCauchySum.sum_shrinks _ _
    (RepresentedCauchySum.sum_shrinks _ _ he he)
    (SeriesLimitLaws.shrinks_scale d hdRate (2*H) (Rat.mul_nonneg (by decide) hH))
  have invnonneg N : 0≤(((N+1:Nat):Rat))⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr (by
    exact_mod_cast (show 0<N+1 by omega)))
  have en N : 0≤e N := Rat.mul_nonneg Rat.natCast_nonneg (invnonneg N)
  have dn N : 0≤d N := Rat.mul_nonneg Rat.natCast_nonneg
    (Rat.mul_nonneg Rat.natCast_nonneg (invnonneg N))
  have rn N : 0≤r N := Rat.mul_nonneg hc (invnonneg N)
  have sn N : 0≤s N := Rat.add_nonneg (Rat.add_nonneg (en N) (en N))
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) (dn N))
  let p := fun N => ScalarSeries.block (pairedIntegerPowerTailRemainder k B a z ha hz) 0 (N+1)
  have vp N : (p N).Valid := ScalarSeries.block_valid _ (pairedIntegerPowerTailRemainder_valid k B a z ha hz) 0 (N+1)
  have vF := pairedIntegerPowerTailValue_valid z hz k B hk hZ
  have vG := pairedIntegerPowerTailValue_valid a ha k B hk hA
  have vD := integerPowerDerivativeTailValue_valid a ha k B hk hA
  have vX := sub_valid z.property a.property
  have vR := SeriesLimitLaws.remainder_valid _ _ _ _ vF vG vD vX
  apply RepresentedCauchySum.unique p vp (fun N => r N+s N)
    (RepresentedCauchySum.sum_shrinks _ _ hr hs) _ _
    (pairedIntegerPowerRemainderTailValue_valid k B a z ha hz hA hZ H hH hd) vR
  · intro N
    exact (pairedIntegerPowerRemainderTailValue_close k B a z ha hz hA hZ H hH hd N).mono
      (add_nonneg_mono _ _ (sn N))
  · intro N
    have h := SeriesLimitLaws.remainder_close _ _ _ _ _ _ _ vF vG vD
      (integerPowerMapTailPrefix_valid z hz k B (N+1))
      (integerPowerMapTailPrefix_valid a ha k B (N+1))
      (integerPowerDerivativeTailPrefix_valid a ha k B (N+1)) vX
      (e N) (e N) (d N) H (dn N) hH
      (integerPowerMapTailPrefix_close z hz k B hk hZ N)
      (integerPowerMapTailPrefix_close a ha k B hk hA N)
      (integerPowerDerivativeTailValue_close a ha k B hk hA N) hd
    have hi := integerPowerTailRemainderPrefix_identity k B (N+1) a z ha hz
    have vQ := SeriesLimitLaws.remainder_valid _ _ _ _
      (integerPowerMapTailPrefix_valid z hz k B (N+1))
      (integerPowerMapTailPrefix_valid a ha k B (N+1))
      (integerPowerDerivativeTailPrefix_valid a ha k B (N+1)) vX
    exact (Small.congr (sub_valid vR vQ) (sub_valid vR (vp N))
      (FunctionTheory.sub_congr (equiv_refl _ vR) (equiv_symm hi)) h).mono
      (remainder_error_mono (e N) (d N) (r N) H (rn N))

end ComputableAnalysis.ModularForms
