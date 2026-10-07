import ComputableAnalysis.ModularForms.PairedOffPoleDomainCoverage
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicLocality

/-! One actual holomorphic lattice map on the entire pole-excluded domain. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedGlobalOffPoleAssemblyMap : DomainFunctions.Map where
  domain := pairedOffPoleDomain
  eval z hz := (pairedOffPoleAssemblyMap (pairedOffPoleCanonicalCutoff z)).eval z
    (pairedOffPoleCanonicalCutoff_mem z hz)
  domain_congr := pairedOffPoleDomain_congr
  eval_congr z w hz hw he := by
    let B := pairedOffPoleCanonicalCutoff z
    let C := pairedOffPoleCanonicalCutoff w
    let hBz := pairedOffPoleCanonicalCutoff_mem z hz
    let hBw := pairedOffPoleAssemblyMap_global_mem B w hw
      (Centered.interior_congr (B:Rat) z w he (pairedOffPoleCanonicalCutoff_interior z))
    let hCw := pairedOffPoleCanonicalCutoff_mem w hw
    exact equiv_trans ((pairedOffPoleAssemblyMap B).eval z hBz).property
      ((pairedOffPoleAssemblyMap B).eval w hBw).property ((pairedOffPoleAssemblyMap C).eval w hCw).property
      ((pairedOffPoleAssemblyMap B).eval_congr z w hBz hBw he)
      (pairedOffPoleAssemblyMap_cutoff_agreement B C w hBw hCw)

theorem pairedGlobalOffPoleAssemblyMap_chart_agreement (B : Nat) (z : Scalar)
    (hz : (pairedOffPoleAssemblyMap B).domain z) :
    ((pairedOffPoleAssemblyMap B).eval z hz).val.Equiv
      (pairedGlobalOffPoleAssemblyMap.eval z (pairedOffPoleAssemblyMap_domain_global B z hz)).val :=
  pairedOffPoleAssemblyMap_cutoff_agreement B (pairedOffPoleCanonicalCutoff z) z hz
    (pairedOffPoleCanonicalCutoff_mem z (pairedOffPoleAssemblyMap_domain_global B z hz))

noncomputable def pairedGlobalOffPoleAssemblyMap_holomorphic : Holomorphic pairedGlobalOffPoleAssemblyMap :=
  holomorphic_of_local pairedGlobalOffPoleAssemblyMap
    (fun a _ => pairedOffPoleAssemblyMap (pairedOffPoleCanonicalCutoff a))
    (fun a _ => pairedOffPoleAssemblyMap_holomorphic (pairedOffPoleCanonicalCutoff a))
    pairedOffPoleCanonicalCutoff_mem
    (fun a _ z hz => pairedOffPoleAssemblyMap_domain_global (pairedOffPoleCanonicalCutoff a) z hz)
    (fun a _ z hz => pairedGlobalOffPoleAssemblyMap_chart_agreement (pairedOffPoleCanonicalCutoff a) z hz)

theorem pairedGlobalOffPoleAssemblyMap_chart_derivative_agreement (B : Nat) (z : Scalar)
    (hz : (pairedOffPoleAssemblyMap B).domain z) :
    ((pairedOffPoleAssemblyMap_holomorphic B).derivative z hz).val.Equiv
      (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z
        (pairedOffPoleAssemblyMap_domain_global B z hz)).val :=
  pairedOffPoleAssemblyMap_cutoff_derivative_agreement B (pairedOffPoleCanonicalCutoff z) z hz
    (pairedOffPoleCanonicalCutoff_mem z (pairedOffPoleAssemblyMap_domain_global B z hz))

noncomputable def pairedGlobalOffPoleAssemblyMap_derivative_holomorphic :
    Holomorphic (derivativeMap pairedGlobalOffPoleAssemblyMap pairedGlobalOffPoleAssemblyMap_holomorphic) :=
  holomorphic_of_local (derivativeMap pairedGlobalOffPoleAssemblyMap pairedGlobalOffPoleAssemblyMap_holomorphic)
    (fun a _ => derivativeMap (pairedOffPoleAssemblyMap (pairedOffPoleCanonicalCutoff a))
      (pairedOffPoleAssemblyMap_holomorphic (pairedOffPoleCanonicalCutoff a)))
    (fun a _ => pairedOffPoleAssemblyMap_derivative_holomorphic (pairedOffPoleCanonicalCutoff a))
    pairedOffPoleCanonicalCutoff_mem
    (fun a _ z hz => pairedOffPoleAssemblyMap_domain_global (pairedOffPoleCanonicalCutoff a) z hz)
    (fun a _ z hz => pairedGlobalOffPoleAssemblyMap_chart_derivative_agreement (pairedOffPoleCanonicalCutoff a) z hz)

theorem pairedGlobalOffPoleAssemblyMap_chart_secondDerivative_agreement (B : Nat) (z : Scalar)
    (hz : (pairedOffPoleAssemblyMap B).domain z) :
    ((pairedOffPoleAssemblyMap_derivative_holomorphic B).derivative z hz).val.Equiv
      (pairedGlobalOffPoleAssemblyMap_derivative_holomorphic.derivative z
        (pairedOffPoleAssemblyMap_domain_global B z hz)).val :=
  pairedOffPoleAssemblyMap_cutoff_secondDerivative_agreement B (pairedOffPoleCanonicalCutoff z) z hz
    (pairedOffPoleCanonicalCutoff_mem z (pairedOffPoleAssemblyMap_domain_global B z hz))

noncomputable def pairedGlobalOffPoleRiccatiMap : DomainFunctions.Map :=
  sumOn (derivativeMap pairedGlobalOffPoleAssemblyMap pairedGlobalOffPoleAssemblyMap_holomorphic)
    (productOn pairedGlobalOffPoleAssemblyMap pairedGlobalOffPoleAssemblyMap (fun _ hz => hz)) (fun _ hz => hz)

noncomputable def pairedGlobalOffPoleRiccatiMap_holomorphic : Holomorphic pairedGlobalOffPoleRiccatiMap :=
  pairedGlobalOffPoleAssemblyMap_derivative_holomorphic.sumOn
    (pairedGlobalOffPoleAssemblyMap_holomorphic.productOn pairedGlobalOffPoleAssemblyMap_holomorphic
      (fun _ hz => hz)) (fun _ hz => hz)

theorem pairedGlobalOffPoleRiccatiMap_chart_agreement (B : Nat) (z : Scalar)
    (hz : (pairedOffPoleAssemblyMap B).domain z) :
    ((pairedOffPoleRiccatiMap B).eval z hz).val.Equiv
      (pairedGlobalOffPoleRiccatiMap.eval z (pairedOffPoleAssemblyMap_domain_global B z hz)).val := by
  have hp := pairedGlobalOffPoleAssemblyMap_chart_agreement B z hz
  exact add_equiv (pairedGlobalOffPoleAssemblyMap_chart_derivative_agreement B z hz)
    (mul_equiv ((pairedOffPoleAssemblyMap B).eval z hz).property
      (pairedGlobalOffPoleAssemblyMap.eval z (pairedOffPoleAssemblyMap_domain_global B z hz)).property
      ((pairedOffPoleAssemblyMap B).eval z hz).property
      (pairedGlobalOffPoleAssemblyMap.eval z (pairedOffPoleAssemblyMap_domain_global B z hz)).property hp hp)

theorem pairedGlobalOffPoleRiccatiMap_chart_derivative_agreement (B : Nat) (z : Scalar)
    (hz : (pairedOffPoleAssemblyMap B).domain z) :
    ((pairedOffPoleRiccatiMap_holomorphic B).derivative z hz).val.Equiv
      (pairedGlobalOffPoleRiccatiMap_holomorphic.derivative z
        (pairedOffPoleAssemblyMap_domain_global B z hz)).val :=
  (pairedOffPoleRiccatiMap_holomorphic B).derivative_equiv_on_overlap
    pairedGlobalOffPoleRiccatiMap_holomorphic
    (fun z hz _ => pairedGlobalOffPoleRiccatiMap_chart_agreement B z hz)
    z hz (pairedOffPoleAssemblyMap_domain_global B z hz)

end ComputableAnalysis.ModularForms
