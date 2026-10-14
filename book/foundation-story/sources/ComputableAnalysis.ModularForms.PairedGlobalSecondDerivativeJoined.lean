import ComputableAnalysis.ModularForms.PairedGlobalDerivativeTailDifferentiable
import ComputableAnalysis.ModularForms.PairedFiniteDerivativeHolomorphic
import ComputableAnalysis.ModularForms.PairedGlobalSecondDerivativeAssembly
import ComputableAnalysis.ModularForms.PairedDerivativeInvariance

/-! Regional assembly of the actual global first-derivative series and its second derivative. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedFiniteFirstDerivativeDiskMap (B : Nat) : DomainFunctions.Map :=
  onDomain (pairedFiniteDerivativeMap (4*B)) (pairedGlobalFirstDerivativeTailMap B).domain_congr
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val ∧ Small z.val (B:Rat)) => hz.1)

def pairedCentralFirstDerivativeDiskMap (B : Nat) : DomainFunctions.Map :=
  onDomain (integerReciprocalDerivativeMap 0) (pairedGlobalFirstDerivativeTailMap B).domain_congr
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val ∧ Small z.val (B:Rat)) => hz.1)

def pairedJoinedFirstDerivativeDiskMap (B : Nat) : DomainFunctions.Map :=
  sumOn (pairedCentralFirstDerivativeDiskMap B)
    (sumOn (pairedFiniteFirstDerivativeDiskMap B) (pairedGlobalFirstDerivativeTailMap B)
      (fun (z : Scalar) (hz : InUpperHalfPlane z.val ∧ Small z.val (B:Rat)) => hz))
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val ∧ Small z.val (B:Rat)) => hz)

private def finiteDiskDerivative (B : Nat) (a : Scalar)
    (ha : (pairedFiniteFirstDerivativeDiskMap B).domain a) :
    HasDerivativeAt (pairedFiniteFirstDerivativeDiskMap B) a ha
      ((pairedFiniteDerivativeMap_holomorphic (4*B)).derivative a ha.1) where
  delta := ((pairedFiniteDerivativeMap_holomorphic (4*B)).atPoint a ha.1).delta
  estimate eps H z hz hH hd :=
    ((pairedFiniteDerivativeMap_holomorphic (4*B)).atPoint a ha.1).estimate eps H z hz.1 hH hd

private def centralDiskDerivative (B : Nat) (a : Scalar)
    (ha : (pairedCentralFirstDerivativeDiskMap B).domain a) :
    HasDerivativeAt (pairedCentralFirstDerivativeDiskMap B) a ha
      ((integerReciprocalDerivativeMap_holomorphic 0).derivative a ha.1) where
  delta := ((integerReciprocalDerivativeMap_holomorphic 0).atPoint a ha.1).delta
  estimate eps H z hz hH hd :=
    ((integerReciprocalDerivativeMap_holomorphic 0).atPoint a ha.1).estimate eps H z hz.1 hH hd

def pairedJoinedFirstDerivativeDiskMap_hasDerivativeAt (B : Nat) (a : Scalar)
    (ha : (pairedJoinedFirstDerivativeDiskMap B).domain a) :
    HasDerivativeAt (pairedJoinedFirstDerivativeDiskMap B) a ha
      (pairedGlobalSecondDerivativeAssembly a ha.1 B ha.2) := by
  let ht := pairedGlobalFirstDerivativeTailMap_hasDerivativeAt B a ha
  let hf := finiteDiskDerivative B a ha
  let hc := centralDiskDerivative B a ha
  let hsum := sumDerivative (pairedFiniteFirstDerivativeDiskMap B) (pairedGlobalFirstDerivativeTailMap B)
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val ∧ Small z.val (B:Rat)) => hz) a ha _ _ hf ht
  let hall := sumDerivative (pairedCentralFirstDerivativeDiskMap B)
    (sumOn (pairedFiniteFirstDerivativeDiskMap B) (pairedGlobalFirstDerivativeTailMap B)
      (fun (z : Scalar) (hz : InUpperHalfPlane z.val ∧ Small z.val (B:Rat)) => hz))
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val ∧ Small z.val (B:Rat)) => hz) a ha _ _ hc hsum
  exact hall.congrDerivative (add_equiv (integerReciprocalDerivativeMap_derivative 0 a ha.1)
    (add_equiv (pairedFiniteDerivativeMap_derivative (4*B) a ha.1)
      (equiv_refl _ (pairedGlobalSecondDerivativeTailValue_valid a ha.1 B ha.2))))

theorem pairedJoinedFirstDerivativeDiskMap_eval (B : Nat) (z : Scalar)
    (hz : (pairedJoinedFirstDerivativeDiskMap B).domain z) :
    ((pairedJoinedFirstDerivativeDiskMap B).eval z hz).val.Equiv
      (pairedWholeJoinedDerivative B z hz).val := by
  have hf := equiv_trans ((pairedFiniteDerivativeMap (4*B)).eval z hz.1).property
    (ScalarSeries.block_valid _ (fun n => (upperPairedReciprocalDerivative z hz.1 (n+1)).property) 0 (4*B))
    ((pairedFiniteMap_holomorphic (4*B)).derivative z hz.1).property
    (pairedFiniteDerivativeMap_eval (4*B) z hz.1)
    (equiv_symm (pairedFiniteMap_derivative (4*B) z hz.1))
  exact add_equiv (integerReciprocalDerivativeMap_eval 0 z hz.1)
    (add_equiv hf (equiv_refl _ (pairedDerivativeTailValue_valid z hz.1 B hz.2)))

theorem pairedJoinedFirstDerivativeDiskMap_canonical (B : Nat) (z : Scalar)
    (hz : (pairedJoinedFirstDerivativeDiskMap B).domain z)
    (hroom : Small z.val ((B:Rat)-1)) :
    ((pairedJoinedFirstDerivativeDiskMap B).eval z hz).val.Equiv
      (pairedPartialFractionDerivative z hz.1).val :=
  equiv_trans ((pairedJoinedFirstDerivativeDiskMap B).eval z hz).property
    (pairedWholeJoinedDerivative B z hz).property (pairedPartialFractionDerivative z hz.1).property
    (pairedJoinedFirstDerivativeDiskMap_eval B z hz)
    (pairedPartialFractionDerivative_cutoff B z hz.1 hroom)

end ComputableAnalysis.ModularForms
