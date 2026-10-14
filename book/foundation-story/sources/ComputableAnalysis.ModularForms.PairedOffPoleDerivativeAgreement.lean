import ComputableAnalysis.ModularForms.PairedOffPoleHolomorphic
import ComputableAnalysis.ModularForms.PairedUpperRiccatiAgreement

/-! Exact derivative agreement of the actual off-pole and canonical lattice constructions. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

noncomputable def pairedOffPoleUpperOpenData (B : Nat) :
    ScalarTopology.OpenData (intersectionSum pairedPartialFractionMap (pairedOffPoleAssemblyMap B)).domain :=
  intersectionOpenData pairedPartialFractionMap_holomorphic (pairedOffPoleAssemblyMap_holomorphic B)

noncomputable def pairedOffPoleUpperCanonicalMap (B : Nat) : DomainFunctions.Map :=
  onDomain pairedPartialFractionMap (pairedOffPoleUpperOpenData B).invariant (fun _ hz => hz.1)

noncomputable def pairedOffPoleUpperCanonicalMap_holomorphic (B : Nat) :
    Holomorphic (pairedOffPoleUpperCanonicalMap B) :=
  pairedPartialFractionMap_holomorphic.onDomain (pairedOffPoleUpperOpenData B) (fun _ hz => hz.1)

private noncomputable def offPoleTransferredHolomorphic (B : Nat) :
    Holomorphic (pairedOffPoleUpperCanonicalMap B) := by
  apply (pairedOffPoleAssemblyMap_holomorphic B).transfer (pairedOffPoleUpperCanonicalMap B)
    (fun _ hz => hz.2) ⟨(pairedOffPoleUpperOpenData B).radius,(pairedOffPoleUpperOpenData B).inside⟩
  intro z hz
  exact pairedOffPoleAssemblyMap_upper_agreement B z hz.1 hz.2.2.2

theorem pairedOffPoleAssemblyMap_upper_derivative_agreement (B : Nat) (z : Scalar)
    (hz : InUpperHalfPlane z.val) (hq : LocalODE.interior (B:Rat) z) :
    ((pairedOffPoleAssemblyMap_holomorphic B).derivative z
      (pairedOffPoleAssemblyMap_upper_mem B z hz hq)).val.Equiv
      (pairedPartialFractionDerivative z hz).val := by
  let hlocal : (pairedOffPoleUpperCanonicalMap B).domain z :=
    ⟨hz,pairedOffPoleAssemblyMap_upper_mem B z hz hq⟩
  exact (offPoleTransferredHolomorphic B).derivative_unique
    (pairedOffPoleUpperCanonicalMap_holomorphic B) z hlocal


noncomputable def pairedOffPoleRiccatiMap (B : Nat) : DomainFunctions.Map where
  domain := (pairedOffPoleAssemblyMap B).domain
  eval z hz := scalarSum ((pairedOffPoleAssemblyMap_holomorphic B).derivative z hz)
    (DomainFunctions.scalarProduct ((pairedOffPoleAssemblyMap B).eval z hz)
      ((pairedOffPoleAssemblyMap B).eval z hz))
  domain_congr := (pairedOffPoleAssemblyMap B).domain_congr
  eval_congr z w hz hw he := add_equiv
    ((pairedOffPoleAssemblyMap_holomorphic B).derivative_congr z w hz hw he)
    (mul_equiv ((pairedOffPoleAssemblyMap B).eval z hz).property
      ((pairedOffPoleAssemblyMap B).eval w hw).property
      ((pairedOffPoleAssemblyMap B).eval z hz).property
      ((pairedOffPoleAssemblyMap B).eval w hw).property
      ((pairedOffPoleAssemblyMap B).eval_congr z w hz hw he)
      ((pairedOffPoleAssemblyMap B).eval_congr z w hz hw he))

theorem pairedOffPoleRiccatiMap_upper_agreement (B : Nat) (z : Scalar)
    (hz : InUpperHalfPlane z.val) (hq : LocalODE.interior (B:Rat) z) :
    ((pairedOffPoleRiccatiMap B).eval z (pairedOffPoleAssemblyMap_upper_mem B z hz hq)).val.Equiv
      (pairedUpperRiccatiValue z hz).val := by
  have hp := pairedOffPoleAssemblyMap_upper_agreement B z hz hq
  exact add_equiv (pairedOffPoleAssemblyMap_upper_derivative_agreement B z hz hq)
    (mul_equiv ((pairedOffPoleAssemblyMap B).eval z (pairedOffPoleAssemblyMap_upper_mem B z hz hq)).property
      (upperPairedPartialFractionValue_valid z hz)
      ((pairedOffPoleAssemblyMap B).eval z (pairedOffPoleAssemblyMap_upper_mem B z hz hq)).property
      (upperPairedPartialFractionValue_valid z hz) hp hp)

end ComputableAnalysis.ModularForms
