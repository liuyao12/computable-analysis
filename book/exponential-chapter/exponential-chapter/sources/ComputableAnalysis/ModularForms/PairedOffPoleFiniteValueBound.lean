import ComputableAnalysis.ModularForms.PairedOutsidePoleReciprocalBounds

/-! Bounds for the finite off-pole value head on the complement of pole charts. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem integerReciprocalOffPoleMap_outside_charts_bound (k : Int) (z : Scalar)
    (hz : (integerReciprocalOffPoleMap k).domain z)
    (hout : ¬∃ j : Int, (pairedIntegerRiccatiExtensionMap j).domain z) :
    Small ((integerReciprocalOffPoleMap k).eval z hz).val 64 :=
  representedInverse_outside_quarter_bound (integerShiftScalar z k)
    (compose_outer_mem hz) (outsideIntegerPoleCharts_shift_not_interior z hout k)

theorem pairedFiniteOffPoleMap_outside_charts_bound (K : Nat) (z : Scalar)
    (hz : (pairedFiniteOffPoleMap K).domain z)
    (hout : ¬∃ j : Int, (pairedIntegerRiccatiExtensionMap j).domain z) :
    Small ((pairedFiniteOffPoleMap K).eval z hz).val ((K:Rat)*128) := by
  induction K with
  | zero =>
    have he : ((pairedFiniteOffPoleMap 0).eval z hz).val.Equiv zero := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := ((pairedFiniteOffPoleMap 0).eval z hz).property)
        (hright := ofQComplex_valid _)
      let Z := ComplexRawQuotient.ofRaw z.val z.property
      change 0+0*Z=0
      grind only
    exact Small.congr (ofQComplex_valid _) ((pairedFiniteOffPoleMap 0).eval z hz).property
      (equiv_symm he) (Small.zero (by decide +kernel))
  | succ K ih =>
    have hs := LocalODE.small_add (ih hz.1)
      (LocalODE.small_add
        (integerReciprocalOffPoleMap_outside_charts_bound _ z hz.2.1 hout)
        (integerReciprocalOffPoleMap_outside_charts_bound _ z hz.2.2 hout))
    have he : (K:Rat)*128+(64+64)=((K+1:Nat):Rat)*128 := by
      rw [Rat.natCast_add,show ((1:Nat):Rat)=1 by decide +kernel]
      grind only
    rw [he] at hs
    exact hs

end ComputableAnalysis.ModularForms
