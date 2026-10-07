import ComputableAnalysis.ModularForms.IntegerPowerJoinedDerivative

/-! Full upper-half-plane differentiation of canonical reciprocal-power rows. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def integerPowerRowMap (k : Nat) (hk : 2≤k) : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval z hz := integerReciprocalPowerRowSum z hz k hk
  domain_congr := upperOpenData.invariant
  eval_congr z w hz hw he := integerReciprocalPowerRowSum_congr z w hz hw he k hk

def integerPowerRowDerivative (k : Nat) (hk : 2≤k) (a : Scalar)
    (ha : InUpperHalfPlane a.val) : Scalar :=
  integerPowerJoinedDerivative k (pairedDerivativeCutoff a) hk a ⟨ha,pairedDerivativeCutoff_small a⟩

theorem integerPowerRowDerivative_next_power (k : Nat) (hk : 2≤k) (a : Scalar)
    (ha : InUpperHalfPlane a.val) :
    (integerPowerRowDerivative k hk a ha).val.Equiv
      (neg (scaleRat (k:Rat) (integerReciprocalPowerRowSum a ha (k+1) (by omega)).val)) :=
  integerPowerJoinedDerivative_next_power k (pairedDerivativeCutoff a) hk a ⟨ha,pairedDerivativeCutoff_small a⟩

def integerPowerRowMap_hasDerivativeAt (k : Nat) (hk : 2≤k) (a : Scalar)
    (ha : InUpperHalfPlane a.val) :
    HasDerivativeAt (integerPowerRowMap k hk) a ha (integerPowerRowDerivative k hk a ha) where
  delta eps := minRadius ⟨1,by decide +kernel⟩
    ((integerPowerJoinedMap_hasDerivativeAt k (pairedDerivativeCutoff a) hk a
      ⟨ha,pairedDerivativeCutoff_small a⟩).delta eps)
  estimate eps H z hz hH hd := by
    have hunit : H.val≤1 := Rat.le_trans hH (minRadius_left _ _)
    have hzB := pairedDerivativeCutoff_neighbor a z (hd.mono hunit)
    let B := pairedDerivativeCutoff a
    let hA : (integerPowerJoinedMap k B hk).domain a := ⟨ha,pairedDerivativeCutoff_small a⟩
    let hZ : (integerPowerJoinedMap k B hk).domain z := ⟨hz,hzB⟩
    have h := (integerPowerJoinedMap_hasDerivativeAt k B hk a hA).estimate eps H z hZ
      (Rat.le_trans hH (minRadius_right _ _)) hd
    have heZ : ((integerPowerJoinedMap k B hk).eval z hZ).val.Equiv
        ((integerPowerRowMap k hk).eval z hz).val :=
      integerPowerRowAssembly_cutoff_agreement z hz k B (pairedDerivativeCutoff z) hk hzB
        (pairedDerivativeCutoff_small z)
    have heA : ((integerPowerJoinedMap k B hk).eval a hA).val.Equiv
        ((integerPowerRowMap k hk).eval a ha).val :=
      equiv_refl _ (integerPowerRowAssembly_valid a ha k B hk (pairedDerivativeCutoff_small a))
    have he := FunctionTheory.sub_congr (FunctionTheory.sub_congr heZ heA)
      (equiv_refl _ (mul_valid (integerPowerRowDerivative k hk a ha).property (sub_valid z.property a.property)))
    exact Small.congr (DomainFunctions.remainder_valid (integerPowerJoinedMap k B hk) a hA
      (integerPowerJoinedDerivative k B hk a hA) z hZ)
      (DomainFunctions.remainder_valid (integerPowerRowMap k hk) a ha (integerPowerRowDerivative k hk a ha) z hz) he h

def integerPowerRowMap_continuous (k : Nat) (hk : 2≤k) :
    ContinuousOn (integerPowerRowMap k hk).domain (integerPowerRowMap k hk).eval :=
  continuousOn_of_derivative (integerPowerRowMap k hk) (integerPowerRowDerivative k hk)
    (integerPowerRowMap_hasDerivativeAt k hk)

end ComputableAnalysis.ModularForms
