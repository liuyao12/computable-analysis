import ComputableAnalysis.ModularForms.PairedStripValueBound
import ComputableAnalysis.ModularForms.PairedUpperDerivativeBound

/-! Uniform upper-region bounds for the actual entire Riccati map. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedUpperRiccatiValue_exact_strip_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val)
    (hre : RealRaw.Le (RealRaw.ofRat 0) z.val.realPart)
    (hhi : RealRaw.Le z.val.realPart (RealRaw.ofRat 2))
    (him : RealRaw.Le (RealRaw.ofRat 2) z.val.imagPart) :
    Small (pairedUpperRiccatiValue z hz).val 324000 := by
  have hp := pairedPartialFractionMap_exact_upper_strip_bound z hz hre hhi him
  have hd := pairedPartialFractionDerivative_exact_upper_strip_bound z hz hre hhi him
  have hs := Small.mul (pairedPartialFractionMap.eval z hz).property
    (pairedPartialFractionMap.eval z hz).property
    (show (0:Rat)≤400 by decide +kernel) (by decide +kernel) hp hp
  exact (LocalODE.small_add hd hs).mono (by decide +kernel)

theorem pairedEntireRiccatiMap_exact_upper_strip_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val)
    (hre : RealRaw.Le (RealRaw.ofRat 0) z.val.realPart)
    (hhi : RealRaw.Le z.val.realPart (RealRaw.ofRat 2))
    (him : RealRaw.Le (RealRaw.ofRat 2) z.val.imagPart) :
    Small (pairedEntireRiccatiMap.eval z trivial).val 324000 := by
  have hg := pairedGlobalOffPole_upper_mem z hz
  have he := equiv_trans (pairedUpperRiccatiValue z hz).property
    (pairedGlobalOffPoleRiccatiMap.eval z hg).property
    (pairedEntireRiccatiMap.eval z trivial).property
    (equiv_symm (pairedGlobalOffPoleRiccatiMap_upper_agreement z hz))
    (pairedEntireRiccatiMap_chart_agreement .offPole z hg)
  exact Small.congr (pairedUpperRiccatiValue z hz).property
    (pairedEntireRiccatiMap.eval z trivial).property he
    (pairedUpperRiccatiValue_exact_strip_bound z hz hre hhi him)

theorem pairedEntireRiccatiMap_above_two_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val)
    (him : RealRaw.Le (RealRaw.ofRat 2) z.val.imagPart) :
    Small (pairedEntireRiccatiMap.eval z trivial).val 324000 := by
  let w := stripRepresentative z
  have hw : InUpperHalfPlane w.val := integerShiftScalar_upper z hz (stripTranslation z)
  have hh := integerShiftScalar_imaginary_lower_bound z (stripTranslation z) 2 him
  have hb := pairedEntireRiccatiMap_exact_upper_strip_bound w hw
    (stripRepresentative_real_bounds z).1 (stripRepresentative_real_bounds z).2 hh
  exact Small.congr (pairedEntireRiccatiMap.eval w trivial).property
    (pairedEntireRiccatiMap.eval z trivial).property (pairedEntireRiccatiMap_strip_agreement z) hb

end ComputableAnalysis.ModularForms
