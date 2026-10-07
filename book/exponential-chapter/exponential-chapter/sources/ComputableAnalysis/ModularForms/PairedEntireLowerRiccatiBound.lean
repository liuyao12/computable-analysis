import ComputableAnalysis.ModularForms.PairedEntireRiccatiReflection

/-! Uniform lower-region bounds obtained from exact entire reflection. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem imaginary_above_two_upper (z : Scalar)
    (him : RealRaw.Le (RealRaw.ofRat 2) z.val.imagPart) : InUpperHalfPlane z.val := by
  obtain ⟨N,hN⟩ := z.property.2.2 ⟨1,by decide +kernel⟩
  have hh := (hN N (Nat.le_refl N)).2
  have hl := him 0 N
  change 2≤(z.val.compute N).hi.im at hl
  change (z.val.compute N).hi.im-(z.val.compute N).lo.im≤1 at hh
  refine ⟨N,?_⟩
  change 0<(z.val.compute N).lo.im
  grind only

theorem pairedReflection_imaginary_below_two (z : Scalar)
    (him : RealRaw.Le z.val.imagPart (RealRaw.ofRat (-2))) :
    RealRaw.Le (RealRaw.ofRat 2) (pairedReflectionMap.eval z trivial).val.imagPart := by
  have he := imagPart_equiv (pairedReflectionMap_eval z)
  have hneg : RealRaw.Le (RealRaw.ofRat 2) (neg z.val).imagPart := by
    intro n m
    have hm := him m 0
    change (z.val.compute m).lo.im≤ -2 at hm
    change 2≤ -(z.val.compute m).lo.im
    grind only
  exact RealRaw.le_trans (imagPart_valid (neg_valid z.property)) hneg
    (RealRaw.le_of_equiv (imagPart_valid (neg_valid z.property))
      (imagPart_valid (pairedReflectionMap.eval z trivial).property) (RealRaw.equiv_symm he))

theorem pairedEntireRiccatiMap_below_minus_two_bound (z : Scalar)
    (him : RealRaw.Le z.val.imagPart (RealRaw.ofRat (-2))) :
    Small (pairedEntireRiccatiMap.eval z trivial).val 324000 := by
  let w := pairedReflectionMap.eval z trivial
  have hw := pairedReflection_imaginary_below_two z him
  have hb := pairedEntireRiccatiMap_above_two_bound w (imaginary_above_two_upper w hw) hw
  exact Small.congr (pairedEntireRiccatiMap.eval w trivial).property
    (pairedEntireRiccatiMap.eval z trivial).property (pairedEntireRiccatiMap_reflection z) hb

theorem pairedEntireRiccatiMap_above_two_bound_exact (z : Scalar)
    (him : RealRaw.Le (RealRaw.ofRat 2) z.val.imagPart) :
    Small (pairedEntireRiccatiMap.eval z trivial).val 324000 :=
  pairedEntireRiccatiMap_above_two_bound z (imaginary_above_two_upper z him) him

end ComputableAnalysis.ModularForms
