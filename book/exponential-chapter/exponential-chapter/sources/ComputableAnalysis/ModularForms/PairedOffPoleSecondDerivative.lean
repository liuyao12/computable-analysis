import ComputableAnalysis.ModularForms.PairedOffPoleTailDerivativeHolomorphic
import ComputableAnalysis.ModularForms.PairedOffPoleDerivativeAgreement

/-! Holomorphic first derivatives of the full off-pole lattice assembly. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private def intersectionDerivativeHolomorphic {f g : DomainFunctions.Map}
    (hf : Holomorphic f) (hg : Holomorphic g)
    (hdf : Holomorphic (derivativeMap f hf)) (hdg : Holomorphic (derivativeMap g hg)) :
    Holomorphic (derivativeMap (intersectionSum f g) (hf.intersectionSum hg)) := by
  let h := hdf.intersectionSum hdg
  apply h.transfer (derivativeMap (intersectionSum f g) (hf.intersectionSum hg))
    (fun _ hz => hz) ⟨(hf.intersectionSum hg).openDomain.radius,(hf.intersectionSum hg).openDomain.inside⟩
  intro z hz
  exact equiv_refl _ ((hf.intersectionSum hg).derivative z hz).property

def integerReciprocalOffPoleMap_derivative_holomorphic (k : Int) :
    Holomorphic (derivativeMap (integerReciprocalOffPoleMap k) (integerReciprocalOffPoleMap_holomorphic k)) := by
  apply (integerReciprocalOffPoleDerivativeMap_holomorphic k).transfer
    (derivativeMap (integerReciprocalOffPoleMap k) (integerReciprocalOffPoleMap_holomorphic k))
    (fun _ hz => hz) ⟨(integerReciprocalOffPoleMap_holomorphic k).openDomain.radius,
      (integerReciprocalOffPoleMap_holomorphic k).openDomain.inside⟩
  intro z hz
  exact equiv_symm (integerReciprocalOffPoleMap_derivative k z hz)

def pairedReciprocalOffPoleTermMap_derivative_holomorphic (n : Nat) :
    Holomorphic (derivativeMap (pairedReciprocalOffPoleTermMap n) (pairedReciprocalOffPoleTermMap_holomorphic n)) :=
  intersectionDerivativeHolomorphic _ _
    (integerReciprocalOffPoleMap_derivative_holomorphic (-((n+1:Nat):Int)))
    (integerReciprocalOffPoleMap_derivative_holomorphic ((n+1:Nat):Int))

def pairedFiniteOffPoleMap_derivative_holomorphic (N : Nat) :
    Holomorphic (derivativeMap (pairedFiniteOffPoleMap N) (pairedFiniteOffPoleMap_holomorphic N)) := by
  induction N with
  | zero =>
    let h := affine_holomorphic ⟨zero,ofQComplex_valid _⟩ ⟨zero,ofQComplex_valid _⟩
    apply h.transfer (derivativeMap (pairedFiniteOffPoleMap 0) (pairedFiniteOffPoleMap_holomorphic 0))
      (fun _ _ => trivial) ⟨(pairedFiniteOffPoleMap_holomorphic 0).openDomain.radius,
        (pairedFiniteOffPoleMap_holomorphic 0).openDomain.inside⟩
    intro z hz
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((affine ⟨zero,ofQComplex_valid _⟩ ⟨zero,ofQComplex_valid _⟩).eval z trivial).property)
      (hright := ((pairedFiniteOffPoleMap_holomorphic 0).derivative z hz).property)
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change 0+0*Z=0
    grind only
  | succ N ih =>
    exact intersectionDerivativeHolomorphic _ _ ih
      (pairedReciprocalOffPoleTermMap_derivative_holomorphic N)

noncomputable def pairedOffPoleAssemblyMap_derivative_holomorphic (B : Nat) :
    Holomorphic (derivativeMap (pairedOffPoleAssemblyMap B) (pairedOffPoleAssemblyMap_holomorphic B)) :=
  intersectionDerivativeHolomorphic _ _ (integerReciprocalOffPoleMap_derivative_holomorphic 0)
    (intersectionDerivativeHolomorphic _ _ (pairedFiniteOffPoleMap_derivative_holomorphic (4*B))
      (pairedOffPoleTailDerivativeMap_holomorphic B))

noncomputable def pairedOffPoleRiccatiMap_holomorphic (B : Nat) : Holomorphic (pairedOffPoleRiccatiMap B) := by
  let hp := pairedOffPoleAssemblyMap_holomorphic B
  let hd := pairedOffPoleAssemblyMap_derivative_holomorphic B
  let h := hd.sumOn (hp.productOn hp (fun _ hz => hz)) (fun _ hz => hz)
  apply h.transfer (pairedOffPoleRiccatiMap B) (fun _ hz => hz) ⟨hp.openDomain.radius,hp.openDomain.inside⟩
  intro z hz
  exact equiv_refl _ ((pairedOffPoleRiccatiMap B).eval z hz).property

end ComputableAnalysis.ModularForms
