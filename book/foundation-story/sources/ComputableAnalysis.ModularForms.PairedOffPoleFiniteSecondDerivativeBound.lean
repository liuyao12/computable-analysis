import ComputableAnalysis.ModularForms.PairedOffPoleReciprocalSecondDerivativeBound

/-! Actual second-derivative bounds for finite off-pole reciprocal heads. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem integerReciprocalOffPoleMap_second_derivative_outside_charts_bound
    (k : Int) (z : Scalar) (hz : (integerReciprocalOffPoleMap k).domain z)
    (hout : ¬∃ j : Int, (pairedIntegerRiccatiExtensionMap j).domain z) :
    Small ((integerReciprocalOffPoleMap_derivative_holomorphic k).derivative z hz).val 2097152 :=
  integerReciprocalOffPoleDerivativeMap_derivative_outside_charts_bound k z hz hout

theorem pairedFiniteOffPoleMap_second_derivative_outside_charts_bound
    (K : Nat) (z : Scalar) (hz : (pairedFiniteOffPoleMap K).domain z)
    (hout : ¬∃ j : Int, (pairedIntegerRiccatiExtensionMap j).domain z) :
    Small ((pairedFiniteOffPoleMap_derivative_holomorphic K).derivative z hz).val
      ((K:Rat)*4194304) := by
  induction K with
  | zero => exact Small.zero (by decide +kernel)
  | succ K ih =>
    have hs := LocalODE.small_add (ih hz.1)
      (LocalODE.small_add
        (integerReciprocalOffPoleMap_second_derivative_outside_charts_bound _ z hz.2.1 hout)
        (integerReciprocalOffPoleMap_second_derivative_outside_charts_bound _ z hz.2.2 hout))
    have he : (K:Rat)*4194304+(2097152+2097152)=((K+1:Nat):Rat)*4194304 := by
      rw [Rat.natCast_add,show ((1:Nat):Rat)=1 by decide +kernel]
      grind only
    rw [he] at hs
    exact hs

theorem pairedOffPoleAssemblyMap_second_derivative_outside_charts_bound
    (B : Nat) (z : Scalar) (hz : (pairedOffPoleAssemblyMap B).domain z)
    (hout : ¬∃ j : Int, (pairedIntegerRiccatiExtensionMap j).domain z) :
    Small ((pairedOffPoleAssemblyMap_derivative_holomorphic B).derivative z hz).val
      (2097152+((4*B:Nat):Rat)*4194304+2*(pairedOffPoleTailSecondDerivativeConstant B:Rat)) := by
  have hs := LocalODE.small_add
    (integerReciprocalOffPoleMap_second_derivative_outside_charts_bound 0 z hz.1 hout)
    (LocalODE.small_add (pairedFiniteOffPoleMap_second_derivative_outside_charts_bound (4*B) z hz.2.1 hout)
      (pairedOffPoleTailSecondDerivativeValue_bound B z hz.2.2))
  exact hs.mono (by grind only)

end ComputableAnalysis.ModularForms
