import ComputableAnalysis.ModularForms.PairedOffPoleFiniteDerivativeBound
import ComputableAnalysis.ModularForms.PairedTailUniformBound

/-! Uniform value estimates for the full finite-plus-tail off-pole assembly. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedOffPoleAssemblyMap_outside_charts_bound (B : Nat) (hB : 0<B) (z : Scalar)
    (hz : (pairedOffPoleAssemblyMap B).domain z)
    (hout : ¬∃ j : Int, (pairedIntegerRiccatiExtensionMap j).domain z) :
    Small ((pairedOffPoleAssemblyMap B).eval z hz).val (68+((4*B:Nat):Rat)*128) := by
  have hs := LocalODE.small_add
    (integerReciprocalOffPoleMap_outside_charts_bound 0 z hz.1 hout)
    (LocalODE.small_add (pairedFiniteOffPoleMap_outside_charts_bound (4*B) z hz.2.1 hout)
      (pairedTailValue_uniform_bound z B (LocalODE.interior_bound _ z hz.2.2) hB))
  exact hs.mono (by grind only)

theorem pairedOffPoleAssemblyMap_three_outside_charts_bound (z : Scalar)
    (hz : (pairedOffPoleAssemblyMap 3).domain z)
    (hout : ¬∃ j : Int, (pairedIntegerRiccatiExtensionMap j).domain z) :
    Small ((pairedOffPoleAssemblyMap 3).eval z hz).val 1604 :=
  (pairedOffPoleAssemblyMap_outside_charts_bound 3 (by decide +kernel) z hz hout).mono
    (by decide +kernel)

end ComputableAnalysis.ModularForms
