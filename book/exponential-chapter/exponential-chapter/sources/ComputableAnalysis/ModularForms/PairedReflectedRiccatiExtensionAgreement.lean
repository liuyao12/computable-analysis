import ComputableAnalysis.ModularForms.PairedReflectedRiccati
import ComputableAnalysis.ModularForms.PairedRiccatiExtensionReflection

/-! Actual lower reflected Riccati values agree with the zero pole extension. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedReflectionMap_interior (R : Rat) (z : Scalar) (hz : LocalODE.interior R z) :
    LocalODE.interior R (pairedReflectionMap.eval z trivial) := by
  obtain ⟨r,hr,hrR,hs⟩ := hz
  exact ⟨r,hr,hrR,Small.congr (neg_valid z.property)
    (pairedReflectionMap.eval z trivial).property (equiv_symm (pairedReflectionMap_eval z))
    (SeriesLimitLaws.small_neg hs)⟩

theorem pairedReflectedRiccati_extension_agreement (z : Scalar)
    (hz : pairedReflectedRiccatiMap.domain z) (hq : LocalODE.interior (1/4) z) :
    (pairedReflectedRiccatiMap.eval z hz).val.Equiv (pairedRiccatiExtension z hq).val := by
  let w := pairedReflectionMap.eval z trivial
  have hw : InUpperHalfPlane w.val := compose_outer_mem hz
  have hwq := pairedReflectionMap_interior (1/4) z hq
  have hp : pairedZeroLaurentMap.domain w := ⟨hwq,upperScalar_nonzero w hw⟩
  exact equiv_trans (pairedReflectedRiccatiMap.eval z hz).property
    (pairedRiccatiExtension w hwq).property (pairedRiccatiExtension z hq).property
    (pairedUpperRiccati_extension_agreement w hp hw)
    (pairedRiccatiExtension_even z w hq hwq (pairedReflectionMap_eval z))

end ComputableAnalysis.ModularForms
