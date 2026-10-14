import ComputableAnalysis.ModularForms.PairedOffPoleFiniteValueBound

/-! Uniform derivative bounds for the finite off-pole head. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem integerReciprocalOffPoleMap_derivative_outside_charts_bound (k : Int) (z : Scalar)
    (hz : (integerReciprocalOffPoleMap k).domain z)
    (hout : ¬∃ j : Int, (pairedIntegerRiccatiExtensionMap j).domain z) :
    Small ((integerReciprocalOffPoleMap_holomorphic k).derivative z hz).val 8192 := by
  have hi := integerReciprocalOffPoleMap_outside_charts_bound k z hz hout
  have hm := Small.mul ((integerReciprocalOffPoleMap k).eval z hz).property
    ((integerReciprocalOffPoleMap k).eval z hz).property
    (show (0:Rat)≤64 by decide +kernel) (show (0:Rat)≤64 by decide +kernel) hi hi
  exact Small.congr (neg_valid (mul_valid ((integerReciprocalOffPoleMap k).eval z hz).property
      ((integerReciprocalOffPoleMap k).eval z hz).property))
    ((integerReciprocalOffPoleMap_holomorphic k).derivative z hz).property
    (equiv_symm (integerReciprocalOffPoleMap_derivative k z hz)) ((SeriesLimitLaws.small_neg hm).mono (by decide +kernel))

theorem pairedFiniteOffPoleMap_derivative_outside_charts_bound (K : Nat) (z : Scalar)
    (hz : (pairedFiniteOffPoleMap K).domain z)
    (hout : ¬∃ j : Int, (pairedIntegerRiccatiExtensionMap j).domain z) :
    Small ((pairedFiniteOffPoleMap_holomorphic K).derivative z hz).val ((K:Rat)*16384) := by
  induction K with
  | zero => exact Small.zero (by decide +kernel)
  | succ K ih =>
    have hs := LocalODE.small_add (ih hz.1)
      (LocalODE.small_add
        (integerReciprocalOffPoleMap_derivative_outside_charts_bound _ z hz.2.1 hout)
        (integerReciprocalOffPoleMap_derivative_outside_charts_bound _ z hz.2.2 hout))
    have he : (K:Rat)*16384+(8192+8192)=((K+1:Nat):Rat)*16384 := by
      rw [Rat.natCast_add,show ((1:Nat):Rat)=1 by decide +kernel]
      grind only
    rw [he] at hs
    exact hs

end ComputableAnalysis.ModularForms
