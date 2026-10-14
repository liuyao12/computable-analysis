import ComputableAnalysis.ModularForms.PairedStripDerivativeBound
import ComputableAnalysis.ModularForms.PairedGlobalOffPoleUpperAgreement

/-! Strip estimates for the derivative of the actual global off-pole map. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedGlobalOffPoleAssemblyMap_derivative_strip_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val) (boxStage : Nat) (R eta : Rat) (heta : 0<eta)
    (him : eta≤(z.val.compute boxStage).lo.im)
    (hre : -R≤(z.val.compute boxStage).lo.re) (hhi : (z.val.compute boxStage).hi.re≤R)
    (K : Nat) (hK : 0<K) (hlarge : 2*R≤((K+1:Nat):Rat)) :
    Small (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z
      (pairedGlobalOffPole_upper_mem z hz)).val
      (2*(8/eta)*(8/eta)+(K:Rat)*(4*(8/eta)*(8/eta))+1024*(K:Rat)⁻¹+2048) :=
  Small.congr (pairedPartialFractionDerivative z hz).property
    (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z (pairedGlobalOffPole_upper_mem z hz)).property
    (equiv_symm (pairedGlobalOffPoleAssemblyMap_upper_derivative_agreement z hz))
    (pairedPartialFractionDerivative_strip_bound z hz boxStage R eta heta him hre hhi K hK hlarge)

theorem pairedGlobalOffPoleAssemblyMap_derivative_upper_strip_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat)
    (him : 1≤(z.val.compute N).lo.im)
    (hre : -3≤(z.val.compute N).lo.re) (hhi : (z.val.compute N).hi.re≤3) :
    Small (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z
      (pairedGlobalOffPole_upper_mem z hz)).val 4000 :=
  Small.congr (pairedPartialFractionDerivative z hz).property
    (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z (pairedGlobalOffPole_upper_mem z hz)).property
    (equiv_symm (pairedGlobalOffPoleAssemblyMap_upper_derivative_agreement z hz))
    (pairedPartialFractionDerivative_upper_strip_bound z hz N him hre hhi)

end ComputableAnalysis.ModularForms
