import ComputableAnalysis.ModularForms.PairedGlobalOffPoleIntegerExtensionAgreement

/-! Distinct integer pole disks are disjoint; actual extension choices agree on overlaps. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem integerQuarterDisk_overlap_unique (j k : Int) (z : Scalar)
    (hj : LocalODE.interior (1/4) (integerShiftScalar z (-j)))
    (hk : LocalODE.interior (1/4) (integerShiftScalar z (-k))) : j=k := by
  let a := integerShiftScalar z (-j)
  let b := integerShiftScalar z (-k)
  have hs := SeriesLimitLaws.small_sub (LocalODE.interior_bound _ a hj) (LocalODE.interior_bound _ b hk)
  have he : (sub a.val b.val).Equiv (rationalInteger (k-j)).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid a.property b.property) (hright := (rationalInteger (k-j)).property)
    change ComplexRawQuotient.ofRaw (integerAffine 1 (-j) z.val) (integerAffine_valid _ _ z.property)-
      ComplexRawQuotient.ofRaw (integerAffine 1 (-k) z.val) (integerAffine_valid _ _ z.property)=
      ComplexRawQuotient.ofQComplex ⟨((k-j:Int):Rat),0⟩
    rw [integerAffine_class,integerAffine_class,integer_constant]
    grind only
  have hc := Small.congr (sub_valid a.property b.property) (rationalInteger (k-j)).property he hs
  have hlo := hc.1 0 0
  have hhi := hc.2.1 0 0
  change -((1:Rat)/4+1/4)≤((k-j:Int):Rat) at hlo
  change ((k-j:Int):Rat)≤(1:Rat)/4+1/4 at hhi
  have hupper : k-j<(1:Int) := by
    exact_mod_cast (show ((k-j:Int):Rat)<((1:Int):Rat) by grind only)
  have hlower : (-1:Int)<k-j := by
    exact_mod_cast (show ((-1:Int):Rat)<((k-j:Int):Rat) by grind only)
  omega

theorem pairedIntegerRiccatiExtensionMap_overlap_unique (j k : Int) (z : Scalar)
    (hj : (pairedIntegerRiccatiExtensionMap j).domain z)
    (hk : (pairedIntegerRiccatiExtensionMap k).domain z) : j=k :=
  integerQuarterDisk_overlap_unique j k z (compose_outer_mem hj) (compose_outer_mem hk)

theorem pairedIntegerRiccatiExtensionMap_overlap_agreement (j k : Int) (z : Scalar)
    (hj : (pairedIntegerRiccatiExtensionMap j).domain z)
    (hk : (pairedIntegerRiccatiExtensionMap k).domain z) :
    ((pairedIntegerRiccatiExtensionMap j).eval z hj).val.Equiv
      ((pairedIntegerRiccatiExtensionMap k).eval z hk).val := by
  have he := pairedIntegerRiccatiExtensionMap_overlap_unique j k z hj hk
  subst k
  exact equiv_refl _ ((pairedIntegerRiccatiExtensionMap j).eval z hj).property

theorem pairedIntegerRiccatiExtensionMap_overlap_derivative_agreement (j k : Int) (z : Scalar)
    (hj : (pairedIntegerRiccatiExtensionMap j).domain z)
    (hk : (pairedIntegerRiccatiExtensionMap k).domain z) :
    ((pairedIntegerRiccatiExtensionMap_holomorphic j).derivative z hj).val.Equiv
      ((pairedIntegerRiccatiExtensionMap_holomorphic k).derivative z hk).val := by
  have he := pairedIntegerRiccatiExtensionMap_overlap_unique j k z hj hk
  subst k
  exact equiv_refl _ ((pairedIntegerRiccatiExtensionMap_holomorphic j).derivative z hj).property

theorem pairedRiccatiCharts_cover (z : Scalar) :
    pairedOffPoleDomain z ∨ ∃ k : Int, (pairedIntegerRiccatiExtensionMap k).domain z := by
  classical
  by_cases hz : pairedOffPoleDomain z
  · exact Or.inl hz
  · have hn : ∃ k : Int, (integerShiftScalar z k).val.Equiv zero := by
      apply Classical.byContradiction
      intro hnone
      apply hz
      apply pairedOffPoleDomain_of_integer_nonzero
      intro k he
      exact hnone ⟨k,he⟩
    obtain ⟨k,hk⟩ := hn
    have hq : LocalODE.interior (1/4) (integerShiftScalar z k) :=
      ⟨0,(by decide +kernel),(by decide +kernel),
        Small.congr (ofQComplex_valid _) (integerShiftScalar z k).property
          (equiv_symm hk) (Small.zero (by decide +kernel))⟩
    refine Or.inr ⟨-k,?_⟩
    refine ⟨trivial,?_⟩
    change LocalODE.interior (1/4) (integerShiftScalar z (-(-k)))
    simpa only [Int.neg_neg] using hq

end ComputableAnalysis.ModularForms
