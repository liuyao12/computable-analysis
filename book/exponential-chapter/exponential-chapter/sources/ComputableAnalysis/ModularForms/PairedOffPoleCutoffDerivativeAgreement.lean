import ComputableAnalysis.ModularForms.PairedOffPoleCutoffAgreement
import ComputableAnalysis.RiemannHilbert.DomainDerivativeOverlap

/-! Cutoff agreement through the second derivative and the actual Riccati expression. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedOffPoleAssemblyMap_cutoff_derivative_agreement (B C : Nat) (z : Scalar)
    (hB : (pairedOffPoleAssemblyMap B).domain z) (hC : (pairedOffPoleAssemblyMap C).domain z) :
    ((pairedOffPoleAssemblyMap_holomorphic B).derivative z hB).val.Equiv
      ((pairedOffPoleAssemblyMap_holomorphic C).derivative z hC).val :=
  (pairedOffPoleAssemblyMap_holomorphic B).derivative_equiv_on_overlap
    (pairedOffPoleAssemblyMap_holomorphic C) (pairedOffPoleAssemblyMap_cutoff_agreement B C) z hB hC

theorem pairedOffPoleAssemblyMap_cutoff_secondDerivative_agreement (B C : Nat) (z : Scalar)
    (hB : (pairedOffPoleAssemblyMap B).domain z) (hC : (pairedOffPoleAssemblyMap C).domain z) :
    ((pairedOffPoleAssemblyMap_derivative_holomorphic B).derivative z hB).val.Equiv
      ((pairedOffPoleAssemblyMap_derivative_holomorphic C).derivative z hC).val :=
  (pairedOffPoleAssemblyMap_derivative_holomorphic B).derivative_equiv_on_overlap
    (pairedOffPoleAssemblyMap_derivative_holomorphic C)
    (pairedOffPoleAssemblyMap_cutoff_derivative_agreement B C) z hB hC

theorem pairedOffPoleRiccatiMap_cutoff_agreement (B C : Nat) (z : Scalar)
    (hB : (pairedOffPoleAssemblyMap B).domain z) (hC : (pairedOffPoleAssemblyMap C).domain z) :
    ((pairedOffPoleRiccatiMap B).eval z hB).val.Equiv
      ((pairedOffPoleRiccatiMap C).eval z hC).val := by
  have hp := pairedOffPoleAssemblyMap_cutoff_agreement B C z hB hC
  exact add_equiv (pairedOffPoleAssemblyMap_cutoff_derivative_agreement B C z hB hC)
    (mul_equiv ((pairedOffPoleAssemblyMap B).eval z hB).property ((pairedOffPoleAssemblyMap C).eval z hC).property
      ((pairedOffPoleAssemblyMap B).eval z hB).property ((pairedOffPoleAssemblyMap C).eval z hC).property hp hp)

theorem pairedOffPoleRiccatiMap_cutoff_derivative_agreement (B C : Nat) (z : Scalar)
    (hB : (pairedOffPoleAssemblyMap B).domain z) (hC : (pairedOffPoleAssemblyMap C).domain z) :
    ((pairedOffPoleRiccatiMap_holomorphic B).derivative z hB).val.Equiv
      ((pairedOffPoleRiccatiMap_holomorphic C).derivative z hC).val :=
  (pairedOffPoleRiccatiMap_holomorphic B).derivative_equiv_on_overlap
    (pairedOffPoleRiccatiMap_holomorphic C) (pairedOffPoleRiccatiMap_cutoff_agreement B C) z hB hC

end ComputableAnalysis.ModularForms
