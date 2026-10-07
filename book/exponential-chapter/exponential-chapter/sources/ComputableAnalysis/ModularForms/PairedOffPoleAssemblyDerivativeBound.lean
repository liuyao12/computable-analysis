import ComputableAnalysis.ModularForms.PairedOffPoleAssemblyValueBound

/-! Bounds on the derivative and Riccati value of the actual off-pole assembly. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedOffPoleAssemblyMap_derivative_outside_charts_bound (B : Nat) (z : Scalar)
    (hz : (pairedOffPoleAssemblyMap B).domain z)
    (hout : ¬∃ j : Int, (pairedIntegerRiccatiExtensionMap j).domain z) :
    Small ((pairedOffPoleAssemblyMap_holomorphic B).derivative z hz).val
      (8192+((4*B:Nat):Rat)*16384+2*(pairedOffPoleTailDerivativeConstant B:Rat)) := by
  have hs := LocalODE.small_add
    (integerReciprocalOffPoleMap_derivative_outside_charts_bound 0 z hz.1 hout)
    (LocalODE.small_add (pairedFiniteOffPoleMap_derivative_outside_charts_bound (4*B) z hz.2.1 hout)
      (pairedOffPoleTailDerivativeValue_bound B z hz.2.2))
  exact hs.mono (by grind only)

theorem pairedOffPoleRiccatiMap_three_outside_charts_bound (z : Scalar)
    (hz : (pairedOffPoleRiccatiMap 3).domain z)
    (hout : ¬∃ j : Int, (pairedIntegerRiccatiExtensionMap j).domain z) :
    Small ((pairedOffPoleRiccatiMap 3).eval z hz).val 5369840 := by
  have hv := pairedOffPoleAssemblyMap_three_outside_charts_bound z hz hout
  have hd := pairedOffPoleAssemblyMap_derivative_outside_charts_bound 3 z hz hout
  have hm := Small.mul ((pairedOffPoleAssemblyMap 3).eval z hz).property
    ((pairedOffPoleAssemblyMap 3).eval z hz).property
    (show (0:Rat)≤1604 by decide +kernel) (show (0:Rat)≤1604 by decide +kernel) hv hv
  exact (LocalODE.small_add hd hm).mono (by decide +kernel)

end ComputableAnalysis.ModularForms
