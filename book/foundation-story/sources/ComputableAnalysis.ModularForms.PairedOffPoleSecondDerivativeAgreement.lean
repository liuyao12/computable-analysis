import ComputableAnalysis.ModularForms.PairedOffPoleSecondDerivative
import ComputableAnalysis.ModularForms.PairedUpperRiccatiDerivative

/-! Exact upper-overlap agreement of second derivatives and Riccati derivatives. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedOffPoleAssemblyMap_upper_secondDerivative_agreement (B : Nat) (z : Scalar)
    (hz : InUpperHalfPlane z.val) (hq : LocalODE.interior (B:Rat) z) :
    ((pairedOffPoleAssemblyMap_derivative_holomorphic B).derivative z
      (pairedOffPoleAssemblyMap_upper_mem B z hz hq)).val.Equiv
      (pairedCanonicalSecondDerivative z hz).val := by
  let ho := pairedOffPoleUpperOpenData B
  let f := onDomain pairedCanonicalFirstDerivativeMap ho.invariant (fun _ hz => hz.1)
  let hg : Holomorphic f := pairedCanonicalFirstDerivativeMap_holomorphic.onDomain ho (fun _ hz => hz.1)
  let hf : Holomorphic f := (pairedOffPoleAssemblyMap_derivative_holomorphic B).transfer f
    (fun _ hz => hz.2) ⟨ho.radius,ho.inside⟩
    (fun z hz => pairedOffPoleAssemblyMap_upper_derivative_agreement B z hz.1 hz.2.2.2)
  exact hf.derivative_unique hg z ⟨hz,pairedOffPoleAssemblyMap_upper_mem B z hz hq⟩

theorem pairedOffPoleRiccatiMap_upper_derivative_agreement (B : Nat) (z : Scalar)
    (hz : InUpperHalfPlane z.val) (hq : LocalODE.interior (B:Rat) z) :
    ((pairedOffPoleRiccatiMap_holomorphic B).derivative z
      (pairedOffPoleAssemblyMap_upper_mem B z hz hq)).val.Equiv
      (pairedUpperRiccatiDerivative z hz).val := by
  let ho := pairedOffPoleUpperOpenData B
  let f := onDomain pairedUpperRiccatiMap ho.invariant (fun _ hz => hz.1)
  let hg : Holomorphic f := pairedUpperRiccatiMap_holomorphic.onDomain ho (fun _ hz => hz.1)
  let hf : Holomorphic f := (pairedOffPoleRiccatiMap_holomorphic B).transfer f
    (fun _ hz => hz.2) ⟨ho.radius,ho.inside⟩
    (fun z hz => pairedOffPoleRiccatiMap_upper_agreement B z hz.1 hz.2.2.2)
  have he := hf.derivative_unique hg z ⟨hz,pairedOffPoleAssemblyMap_upper_mem B z hz hq⟩
  exact equiv_trans
    ((pairedOffPoleRiccatiMap_holomorphic B).derivative z
      (pairedOffPoleAssemblyMap_upper_mem B z hz hq)).property
    (pairedUpperRiccatiMap_holomorphic.derivative z hz).property
    (pairedUpperRiccatiDerivative z hz).property he (pairedUpperRiccatiMap_derivative z hz)

end ComputableAnalysis.ModularForms
