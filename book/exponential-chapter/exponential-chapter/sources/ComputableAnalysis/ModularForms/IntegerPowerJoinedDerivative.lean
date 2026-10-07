import ComputableAnalysis.ModularForms.IntegerPowerTailDerivative

/-! Differentiable full reciprocal-power row assembly and its next-power slope. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def integerPowerFiniteDiskMap (k B : Nat) (hk : 2≤k) : DomainFunctions.Map :=
  onDomain (integerPowerFiniteRowMap k (4*B)) (integerPowerTailDiskMap k B hk).domain_congr
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val ∧ Small z.val (B:Rat)) => hz.1)

def integerPowerFiniteDiskMap_hasDerivativeAt (k B : Nat) (hk : 2≤k) (a : Scalar)
    (ha : (integerPowerFiniteDiskMap k B hk).domain a) :
    HasDerivativeAt (integerPowerFiniteDiskMap k B hk) a ha
      ((integerPowerFiniteRowMap_holomorphic k (4*B)).derivative a ha.1) where
  delta := ((integerPowerFiniteRowMap_holomorphic k (4*B)).atPoint a ha.1).delta
  estimate eps H z hz hH hd :=
    ((integerPowerFiniteRowMap_holomorphic k (4*B)).atPoint a ha.1).estimate eps H z hz.1 hH hd

def integerPowerJoinedMap (k B : Nat) (hk : 2≤k) : DomainFunctions.Map :=
  sumOn (integerPowerFiniteDiskMap k B hk) (integerPowerTailDiskMap k B hk)
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val ∧ Small z.val (B:Rat)) => hz)

def integerPowerJoinedDerivative (k B : Nat) (hk : 2≤k)
    (a : Scalar) (ha : (integerPowerJoinedMap k B hk).domain a) : Scalar :=
  scalarSum ((integerPowerFiniteRowMap_holomorphic k (4*B)).derivative a ha.1)
    (integerPowerTailDiskDerivative k B hk a ha)

def integerPowerJoinedMap_hasDerivativeAt (k B : Nat) (hk : 2≤k)
    (a : Scalar) (ha : (integerPowerJoinedMap k B hk).domain a) :
    HasDerivativeAt (integerPowerJoinedMap k B hk) a ha (integerPowerJoinedDerivative k B hk a ha) :=
  sumDerivative (integerPowerFiniteDiskMap k B hk) (integerPowerTailDiskMap k B hk)
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val ∧ Small z.val (B:Rat)) => hz)
    a ha _ _ (integerPowerFiniteDiskMap_hasDerivativeAt k B hk a ha)
    (integerPowerTailDiskMap_hasDerivativeAt k B hk a ha)

theorem integerPowerJoinedMap_eval (k B : Nat) (hk : 2≤k)
    (z : Scalar) (hz : (integerPowerJoinedMap k B hk).domain z) :
    ((integerPowerJoinedMap k B hk).eval z hz).val=integerPowerRowAssembly z hz.1 k B := rfl

theorem integerPowerJoinedDerivative_next_power (k B : Nat) (hk : 2≤k)
    (a : Scalar) (ha : (integerPowerJoinedMap k B hk).domain a) :
    (integerPowerJoinedDerivative k B hk a ha).val.Equiv
      (neg (scaleRat (k:Rat) (integerPowerRowAssembly a ha.1 (k+1) B))) := by
  let p := integerPowerRowPrefix a ha.1 (k+1) (4*B)
  let t := pairedIntegerPowerTailValue a ha.1 (k+1) B
  have vp := integerPowerRowPrefix_valid a ha.1 (k+1) (4*B)
  have vt := pairedIntegerPowerTailValue_valid a ha.1 (k+1) B (by omega) ha.2
  have h : (integerPowerJoinedDerivative k B hk a ha).val.Equiv
      (add (neg (scaleRat (k:Rat) p)) (neg (scaleRat (k:Rat) t))) :=
    add_equiv (integerPowerFiniteRowMap_derivative a ha.1 k (4*B))
      (equiv_refl _ (neg_valid (scaleRat_valid (r := (k:Rat)) vt)))
  apply equiv_trans (integerPowerJoinedDerivative k B hk a ha).property
    (add_valid (neg_valid (scaleRat_valid (r := (k:Rat)) vp))
      (neg_valid (scaleRat_valid (r := (k:Rat)) vt)))
    (neg_valid (scaleRat_valid (r := (k:Rat)) (integerPowerRowAssembly_valid a ha.1 (k+1) B (by omega) ha.2))) h
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := add_valid (neg_valid (scaleRat_valid (r := (k:Rat)) vp))
      (neg_valid (scaleRat_valid (r := (k:Rat)) vt)))
    (hright := neg_valid (scaleRat_valid (r := (k:Rat))
      (integerPowerRowAssembly_valid a ha.1 (k+1) B (by omega) ha.2)))
  let P := ComplexRawQuotient.ofRaw p vp
  let T := ComplexRawQuotient.ofRaw t vt
  change -ComplexRawQuotient.scaleRat (k:Rat) P+ -ComplexRawQuotient.scaleRat (k:Rat) T=
    -ComplexRawQuotient.scaleRat (k:Rat) (P+T)
  rw [ComplexRawQuotient.scaleRat_add]
  generalize ComplexRawQuotient.scaleRat (k:Rat) P=u,ComplexRawQuotient.scaleRat (k:Rat) T=v
  grind only

end ComputableAnalysis.ModularForms
