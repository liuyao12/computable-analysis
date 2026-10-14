import ComputableAnalysis.ModularForms.PairedUpperStripSecondDerivativeBound

/-! Uniform entire Riccati derivative bounds on the upper outer region. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedUpperRiccatiDerivative_exact_strip_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val)
    (hre : RealRaw.Le (RealRaw.ofRat 0) z.val.realPart)
    (hhi : RealRaw.Le z.val.realPart (RealRaw.ofRat 2))
    (him : RealRaw.Le (RealRaw.ofRat 2) z.val.imagPart) :
    Small (pairedUpperRiccatiDerivative z hz).val 6764544 := by
  have hp := pairedPartialFractionMap_exact_upper_strip_bound z hz hre hhi him
  have hd := pairedPartialFractionDerivative_exact_upper_strip_bound z hz hre hhi him
  have hs := pairedCanonicalSecondDerivative_exact_upper_strip_bound z hz hre hhi him
  have hm := Small.mul (pairedPartialFractionMap.eval z hz).property
    (pairedPartialFractionDerivative z hz).property
    (show (0:Rat)≤400 by decide +kernel) (show (0:Rat)≤4000 by decide +kernel) hp hd
  exact (LocalODE.small_add hs (LocalODE.small_add hm hm)).mono (by decide +kernel)

theorem pairedEntireRiccatiMap_exact_upper_strip_derivative_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val)
    (hre : RealRaw.Le (RealRaw.ofRat 0) z.val.realPart)
    (hhi : RealRaw.Le z.val.realPart (RealRaw.ofRat 2))
    (him : RealRaw.Le (RealRaw.ofRat 2) z.val.imagPart) :
    Small (pairedEntireRiccatiMap_holomorphic.derivative z trivial).val 6764544 := by
  have hd := pairedGlobalOffPole_upper_mem z hz
  have he := equiv_trans (pairedUpperRiccatiDerivative z hz).property
    (pairedGlobalOffPoleRiccatiMap_holomorphic.derivative z hd).property
    (pairedEntireRiccatiMap_holomorphic.derivative z trivial).property
    (equiv_symm (pairedGlobalOffPoleRiccatiMap_upper_derivative_agreement z hz))
    (pairedEntireRiccatiMap_chart_derivative_agreement .offPole z hd)
  exact Small.congr (pairedUpperRiccatiDerivative z hz).property
    (pairedEntireRiccatiMap_holomorphic.derivative z trivial).property he
    (pairedUpperRiccatiDerivative_exact_strip_bound z hz hre hhi him)

theorem pairedEntireRiccatiMap_above_two_derivative_bound (z : Scalar)
    (him : RealRaw.Le (RealRaw.ofRat 2) z.val.imagPart) :
    Small (pairedEntireRiccatiMap_holomorphic.derivative z trivial).val 6764544 := by
  let w := stripRepresentative z
  have hi := integerShiftScalar_imaginary_lower_bound z (stripTranslation z) 2 him
  have hb := pairedEntireRiccatiMap_exact_upper_strip_derivative_bound w
    (imaginary_above_two_upper w hi) (stripRepresentative_real_bounds z).1
    (stripRepresentative_real_bounds z).2 hi
  exact Small.congr (pairedEntireRiccatiMap_holomorphic.derivative w trivial).property
    (pairedEntireRiccatiMap_holomorphic.derivative z trivial).property
    (pairedEntireRiccatiMap_derivative_period_int (stripTranslation z) z) hb

end ComputableAnalysis.ModularForms
