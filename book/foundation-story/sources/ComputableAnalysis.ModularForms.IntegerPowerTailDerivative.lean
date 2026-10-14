import ComputableAnalysis.ModularForms.IntegerPowerTailRemainderIdentity

/-! Actual differentiability of constructed reciprocal-power tails. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def integerPowerTailDiskMap (k B : Nat) (hk : 2≤k) : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val ∧ Small z.val (B:Rat)
  eval z hz := ⟨pairedIntegerPowerTailValue z hz.1 k B,
    pairedIntegerPowerTailValue_valid z hz.1 k B hk hz.2⟩
  domain_congr z w he := by
    constructor
    · intro h
      exact ⟨(upperOpenData.invariant z w he).mp h.1,Small.congr z.property w.property he h.2⟩
    · intro h
      exact ⟨(upperOpenData.invariant z w he).mpr h.1,Small.congr w.property z.property (equiv_symm he) h.2⟩
  eval_congr z w hz hw he := pairedIntegerPowerTailValue_congr z w hz.1 hw.1 he k B hk hz.2 hw.2

def integerPowerTailDiskDerivative (k B : Nat) (hk : 2≤k)
    (a : Scalar) (ha : (integerPowerTailDiskMap k B hk).domain a) : Scalar :=
  ⟨integerPowerDerivativeTailValue a ha.1 k B,integerPowerDerivativeTailValue_valid a ha.1 k B hk ha.2⟩

private theorem positive_margin (C : Rat) (hC : 0≤C) : 0<C+1 := by grind only
private theorem quadratic_to_linear (C H eps D : Rat) (hC : 0≤C) (hH : 0≤H)
    (hHD : H≤D) (hD : (C+1)*D=eps) : C*H*H≤eps*H := by
  have hm := Rat.mul_le_mul_of_nonneg_left hHD (Rat.le_of_lt (positive_margin C hC))
  rw [hD] at hm
  have hstep : C*H≤(C+1)*H := by grind only
  exact Rat.mul_le_mul_of_nonneg_right (Rat.le_trans hstep hm) hH

def integerPowerTailDiskMap_hasDerivativeAt (k B : Nat) (hk : 2≤k)
    (a : Scalar) (ha : (integerPowerTailDiskMap k B hk).domain a) :
    HasDerivativeAt (integerPowerTailDiskMap k B hk) a ha (integerPowerTailDiskDerivative k B hk a ha) where
  delta eps := divideRadius eps ⟨4*powerRemainderCoefficient 16 k+1,
    positive_margin _ (Rat.mul_nonneg (by decide) (powerRemainderCoefficient_nonnegative 16 (by decide) k))⟩
  estimate eps H z hz hH hd := by
    have hi := integerPowerTailRemainder_identity k B hk a z ha.1 hz.1 ha.2 hz.2
      H.val (Rat.le_of_lt H.property) hd
    have hb := pairedIntegerPowerRemainderTailValue_bound k B a z ha.1 hz.1 ha.2 hz.2
      H.val (Rat.le_of_lt H.property) hd
    have h := Small.congr
      (pairedIntegerPowerRemainderTailValue_valid k B a z ha.1 hz.1 ha.2 hz.2
        H.val (Rat.le_of_lt H.property) hd)
      (DomainFunctions.remainder_valid (integerPowerTailDiskMap k B hk) a ha
        (integerPowerTailDiskDerivative k B hk a ha) z hz) hi hb
    apply h.mono
    exact quadratic_to_linear _ _ _ _
      (Rat.mul_nonneg (by decide) (powerRemainderCoefficient_nonnegative 16 (by decide) k))
      (Rat.le_of_lt H.property) hH (divideRadius_identity eps ⟨4*powerRemainderCoefficient 16 k+1,
        positive_margin _ (Rat.mul_nonneg (by decide) (powerRemainderCoefficient_nonnegative 16 (by decide) k))⟩)

end ComputableAnalysis.ModularForms
