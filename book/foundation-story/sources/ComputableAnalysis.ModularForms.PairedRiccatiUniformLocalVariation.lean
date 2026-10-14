import ComputableAnalysis.ModularForms.PairedEntireGlobalDerivativeBound

/-! One global local-variation coefficient derived from actual derivative evidence. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedEntireRiccatiMap_uniform_local_variation (a z : Scalar) (H : QPos)
    (hH : H.val≤((pairedEntireRiccatiMap_holomorphic.atPoint a trivial).delta unitError).val)
    (hza : Small (sub z.val a.val) H.val) :
    Small (sub (pairedEntireRiccatiMap.eval z trivial).val
      (pairedEntireRiccatiMap.eval a trivial).val) (2854864385*H.val) := by
  let d := pairedEntireRiccatiMap_holomorphic.derivative a trivial
  have hr := (pairedEntireRiccatiMap_holomorphic.atPoint a trivial).estimate unitError H z trivial hH hza
  have hd := Small.mul d.property (sub_valid z.property a.property)
    (show (0:Rat)≤1427432192 by decide +kernel) (Rat.le_of_lt H.property)
    (pairedEntireRiccatiMap_global_derivative_bound a) hza
  have hs := LocalODE.small_add hd hr
  have he := difference_remainder pairedEntireRiccatiMap a trivial d z trivial
  exact (Small.congr
    (add_valid (mul_valid d.property (sub_valid z.property a.property))
      (remainder_valid pairedEntireRiccatiMap a trivial d z trivial))
    (sub_valid (pairedEntireRiccatiMap.eval z trivial).property (pairedEntireRiccatiMap.eval a trivial).property)
    (equiv_symm he) hs).mono (by unfold unitError; grind only)

end ComputableAnalysis.ModularForms
