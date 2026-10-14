import ComputableAnalysis.ModularForms.IntegerReciprocalOffPole
import ComputableAnalysis.ModularForms.PairedFiniteHolomorphic
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicIntersectionSum

/-! Finite lattice reciprocal sums on the intersections of their full off-pole domains. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedReciprocalOffPoleTermMap (n : Nat) : DomainFunctions.Map :=
  intersectionSum (integerReciprocalOffPoleMap (-((n+1:Nat):Int)))
    (integerReciprocalOffPoleMap ((n+1:Nat):Int))

def pairedReciprocalOffPoleTermMap_holomorphic (n : Nat) : Holomorphic (pairedReciprocalOffPoleTermMap n) :=
  (integerReciprocalOffPoleMap_holomorphic (-((n+1:Nat):Int))).intersectionSum
    (integerReciprocalOffPoleMap_holomorphic ((n+1:Nat):Int))

def pairedFiniteOffPoleMap : Nat → DomainFunctions.Map
  | 0 => affine ⟨zero,ofQComplex_valid _⟩ ⟨zero,ofQComplex_valid _⟩
  | N+1 => intersectionSum (pairedFiniteOffPoleMap N) (pairedReciprocalOffPoleTermMap N)

def pairedFiniteOffPoleMap_holomorphic (N : Nat) : Holomorphic (pairedFiniteOffPoleMap N) := by
  induction N with
  | zero => exact affine_holomorphic ⟨zero,ofQComplex_valid _⟩ ⟨zero,ofQComplex_valid _⟩
  | succ N ih => exact ih.intersectionSum (pairedReciprocalOffPoleTermMap_holomorphic N)

def pairedFiniteOffPoleMap_upper_mem (N : Nat) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (pairedFiniteOffPoleMap N).domain z := by
  induction N with
  | zero => exact trivial
  | succ N ih => exact ⟨ih,integerReciprocalOffPoleMap_upper_mem _ z hz,
      integerReciprocalOffPoleMap_upper_mem _ z hz⟩

theorem pairedFiniteOffPoleMap_upper_agreement (N : Nat) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ((pairedFiniteOffPoleMap N).eval z (pairedFiniteOffPoleMap_upper_mem N z hz)).val.Equiv
      ((pairedFiniteMap N).eval z hz).val := by
  induction N with
  | zero =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((pairedFiniteOffPoleMap 0).eval z (pairedFiniteOffPoleMap_upper_mem 0 z hz)).property)
      (hright := ((pairedFiniteMap 0).eval z hz).property)
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change 0+0*Z=0
    grind only
  | succ N ih =>
    have ht := add_equiv (integerReciprocalOffPoleMap_upper_agreement (-((N+1:Nat):Int)) z hz)
      (integerReciprocalOffPoleMap_upper_agreement ((N+1:Nat):Int) z hz)
    have h := add_equiv ih ht
    simpa only [pairedFiniteOffPoleMap,intersectionSum,pairedReciprocalOffPoleTermMap,
      pairedFiniteMap,ScalarSeries.block.eq_2,Nat.zero_add,scalarSum,
      pairedReciprocalTermMap,sumOn] using h


theorem pairedFiniteOffPoleMap_upper_derivative_agreement (N : Nat) (z : Scalar)
    (hz : InUpperHalfPlane z.val) :
    ((pairedFiniteOffPoleMap_holomorphic N).derivative z
      (pairedFiniteOffPoleMap_upper_mem N z hz)).val.Equiv
      ((pairedFiniteMap_holomorphic N).derivative z hz).val := by
  let hf : Holomorphic (pairedFiniteMap N) :=
    (pairedFiniteOffPoleMap_holomorphic N).transfer (pairedFiniteMap N)
      (fun z hz => pairedFiniteOffPoleMap_upper_mem N z hz)
      (pairedFiniteMap_holomorphic N).openDomain
      (fun z hz => pairedFiniteOffPoleMap_upper_agreement N z hz)
  exact hf.derivative_unique (pairedFiniteMap_holomorphic N) z hz

theorem pairedFiniteOffPoleMap_upper_derivative_series (N : Nat) (z : Scalar)
    (hz : InUpperHalfPlane z.val) :
    ((pairedFiniteOffPoleMap_holomorphic N).derivative z
      (pairedFiniteOffPoleMap_upper_mem N z hz)).val.Equiv
      (ScalarSeries.block (fun n => (upperPairedReciprocalDerivative z hz (n+1)).val) 0 N) :=
  equiv_trans
    ((pairedFiniteOffPoleMap_holomorphic N).derivative z (pairedFiniteOffPoleMap_upper_mem N z hz)).property
    ((pairedFiniteMap_holomorphic N).derivative z hz).property
    (ScalarSeries.block_valid _ (fun n => (upperPairedReciprocalDerivative z hz (n+1)).property) 0 N)
    (pairedFiniteOffPoleMap_upper_derivative_agreement N z hz) (pairedFiniteMap_derivative N z hz)

end ComputableAnalysis.ModularForms
