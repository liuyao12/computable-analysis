import ComputableAnalysis.ModularForms.PairedFiniteHolomorphic

/-! Differentiable assembly of the finite initial sum and the actual reciprocal tail. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedFiniteDiskMap (B : Nat) : DomainFunctions.Map :=
  onDomain (pairedFiniteMap (4*B)) (pairedTailDiskMap B).domain_congr
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val ∧ Small z.val (B:Rat)) => hz.1)

def pairedFiniteDiskMap_hasDerivativeAt (B : Nat) (a : Scalar)
    (ha : (pairedFiniteDiskMap B).domain a) :
    HasDerivativeAt (pairedFiniteDiskMap B) a ha
      ((pairedFiniteMap_holomorphic (4*B)).derivative a ha.1) where
  delta := ((pairedFiniteMap_holomorphic (4*B)).atPoint a ha.1).delta
  estimate eps H z hz hH hd :=
    ((pairedFiniteMap_holomorphic (4*B)).atPoint a ha.1).estimate eps H z hz.1 hH hd

def pairedJoinedMap (B : Nat) : DomainFunctions.Map :=
  sumOn (pairedFiniteDiskMap B) (pairedTailDiskMap B)
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val ∧ Small z.val (B:Rat)) => hz)

def pairedJoinedDerivative (B : Nat) (a : Scalar) (ha : (pairedJoinedMap B).domain a) : Scalar :=
  scalarSum ((pairedFiniteMap_holomorphic (4*B)).derivative a ha.1)
    (pairedTailDiskDerivative B a ha)

def pairedJoinedMap_hasDerivativeAt (B : Nat) (a : Scalar) (ha : (pairedJoinedMap B).domain a) :
    HasDerivativeAt (pairedJoinedMap B) a ha (pairedJoinedDerivative B a ha) :=
  sumDerivative (pairedFiniteDiskMap B) (pairedTailDiskMap B)
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val ∧ Small z.val (B:Rat)) => hz)
    a ha _ _ (pairedFiniteDiskMap_hasDerivativeAt B a ha) (pairedTailDiskMap_hasDerivativeAt B a ha)

theorem pairedJoinedMap_eval (B : Nat) (z : Scalar) (hz : (pairedJoinedMap B).domain z) :
    ((pairedJoinedMap B).eval z hz).val.Equiv
      (pairedFullValue z (upperPairedSeriesDomain z hz.1) B hz.2) := by
  have h := equiv_trans ((pairedFiniteMap (4*B)).eval z hz.1).property
    (upperPairedLatticePrefix_valid z hz.1 (4*B))
    (ScalarSeries.block_valid _ (fun n => (pairedFullTerm z (upperPairedSeriesDomain z hz.1) n).property) 0 (4*B))
    (pairedFiniteMap_eval (4*B) z hz.1) (upperPairedLatticePrefix_agreement z hz.1 (4*B))
  exact add_equiv h (equiv_refl _ (pairedTailValue_valid z B hz.2))

theorem pairedJoinedDerivative_formula (B : Nat) (a : Scalar) (ha : (pairedJoinedMap B).domain a) :
    (pairedJoinedDerivative B a ha).val.Equiv
      (add (ScalarSeries.block (fun n => (upperPairedReciprocalDerivative a ha.1 (n+1)).val) 0 (4*B))
        (pairedDerivativeTailValue a ha.1 B)) :=
  add_equiv (pairedFiniteMap_derivative (4*B) a ha.1)
    (equiv_refl _ (pairedDerivativeTailValue_valid a ha.1 B ha.2))

def pairedCenterDiskMap (B : Nat) : DomainFunctions.Map :=
  onDomain (integerReciprocalMap 0) (pairedTailDiskMap B).domain_congr
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val ∧ Small z.val (B:Rat)) => hz.1)

def pairedCenterDiskMap_hasDerivativeAt (B : Nat) (a : Scalar)
    (ha : (pairedCenterDiskMap B).domain a) :
    HasDerivativeAt (pairedCenterDiskMap B) a ha
      ((integerReciprocalMap_holomorphic 0).derivative a ha.1) where
  delta := ((integerReciprocalMap_holomorphic 0).atPoint a ha.1).delta
  estimate eps H z hz hH hd :=
    ((integerReciprocalMap_holomorphic 0).atPoint a ha.1).estimate eps H z hz.1 hH hd

def pairedWholeJoinedMap (B : Nat) : DomainFunctions.Map :=
  sumOn (pairedCenterDiskMap B) (pairedJoinedMap B)
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val ∧ Small z.val (B:Rat)) => hz)

def pairedWholeJoinedDerivative (B : Nat) (a : Scalar)
    (ha : (pairedWholeJoinedMap B).domain a) : Scalar :=
  scalarSum ((integerReciprocalMap_holomorphic 0).derivative a ha.1)
    (pairedJoinedDerivative B a ha)

def pairedWholeJoinedMap_hasDerivativeAt (B : Nat) (a : Scalar)
    (ha : (pairedWholeJoinedMap B).domain a) :
    HasDerivativeAt (pairedWholeJoinedMap B) a ha (pairedWholeJoinedDerivative B a ha) :=
  sumDerivative (pairedCenterDiskMap B) (pairedJoinedMap B)
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val ∧ Small z.val (B:Rat)) => hz)
    a ha _ _ (pairedCenterDiskMap_hasDerivativeAt B a ha) (pairedJoinedMap_hasDerivativeAt B a ha)

theorem pairedWholeJoinedMap_eval (B : Nat) (z : Scalar) (hz : (pairedWholeJoinedMap B).domain z) :
    ((pairedWholeJoinedMap B).eval z hz).val.Equiv (upperPairedPartialFractionValue z hz.1) := by
  have h := equiv_trans ((pairedJoinedMap B).eval z hz).property
    (pairedFullValue_valid z (upperPairedSeriesDomain z hz.1) B hz.2)
    (pairedSeriesValue_valid z (upperPairedSeriesDomain z hz.1))
    (pairedJoinedMap_eval B z hz)
    (equiv_symm (pairedSeriesValue_agrees z (upperPairedSeriesDomain z hz.1) B hz.2))
  exact add_equiv (upperIntegerReciprocal_zero z hz.1) h

end ComputableAnalysis.ModularForms
