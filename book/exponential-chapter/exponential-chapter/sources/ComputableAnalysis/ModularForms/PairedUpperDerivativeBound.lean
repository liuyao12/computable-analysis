import ComputableAnalysis.ModularForms.PairedExactUpperStripDerivativeBound
import ComputableAnalysis.ModularForms.PairedRiccatiStripReduction

/-! Uniform derivative bounds on the whole region above height two. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem integerShiftScalar_imaginary_lower_bound (z : Scalar) (k : Int) (a : Rat)
    (ha : RealRaw.Le (RealRaw.ofRat a) z.val.imagPart) :
    RealRaw.Le (RealRaw.ofRat a) (integerShiftScalar z k).val.imagPart := by
  intro m n
  have h := ha m n
  simpa only [integerShiftScalar,integerAffine,translate,scaleRat,QBox.scaleRat,imagPart,
    add,ofQComplex,QBox.add,QComplex.add,Rat.intCast_one,
    if_pos (show (0:Rat)≤1 by decide),Rat.one_mul,Rat.add_zero] using h

theorem pairedGlobalOffPoleAssemblyMap_derivative_above_two_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val)
    (him : RealRaw.Le (RealRaw.ofRat 2) z.val.imagPart) :
    Small (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z
      (pairedGlobalOffPole_upper_mem z hz)).val 4000 := by
  let w := stripRepresentative z
  have hw : InUpperHalfPlane w.val := integerShiftScalar_upper z hz (stripTranslation z)
  have hh : RealRaw.Le (RealRaw.ofRat 2) w.val.imagPart :=
    integerShiftScalar_imaginary_lower_bound z (stripTranslation z) 2 him
  have hb := pairedGlobalOffPoleAssemblyMap_derivative_exact_upper_strip_bound w hw
    (stripRepresentative_real_bounds z).1 (stripRepresentative_real_bounds z).2 hh
  exact Small.congr
    (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative w (pairedGlobalOffPole_upper_mem w hw)).property
    (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z (pairedGlobalOffPole_upper_mem z hz)).property
    (pairedGlobalOffPoleAssemblyMap_derivative_period_int (stripTranslation z) z
      (pairedGlobalOffPole_upper_mem z hz)) hb

theorem pairedPartialFractionDerivative_above_two_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val)
    (him : RealRaw.Le (RealRaw.ofRat 2) z.val.imagPart) :
    Small (pairedPartialFractionDerivative z hz).val 4000 :=
  Small.congr
    (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z (pairedGlobalOffPole_upper_mem z hz)).property
    (pairedPartialFractionDerivative z hz).property
    (pairedGlobalOffPoleAssemblyMap_upper_derivative_agreement z hz)
    (pairedGlobalOffPoleAssemblyMap_derivative_above_two_bound z hz him)

end ComputableAnalysis.ModularForms
