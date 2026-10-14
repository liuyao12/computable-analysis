import ComputableAnalysis.ModularForms.PairedEntireLowerRiccatiBound

/-! The exact middle band reduces to a fixed bounded input box. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem exactMiddleStrip_small (z : Scalar)
    (hre : RealRaw.Le (RealRaw.ofRat 0) z.val.realPart)
    (hhi : RealRaw.Le z.val.realPart (RealRaw.ofRat 2))
    (hlo : RealRaw.Le (RealRaw.ofRat (-2)) z.val.imagPart)
    (hup : RealRaw.Le z.val.imagPart (RealRaw.ofRat 2)) : Small z.val 2 := by
  refine ⟨?_,hhi,hlo,hup⟩
  intro n m
  have h := hre n m
  change 0≤(z.val.compute m).hi.re at h
  change -2≤(z.val.compute m).hi.re
  grind only

theorem integerShiftScalar_imaginary_upper_bound (z : Scalar) (k : Int) (a : Rat)
    (ha : RealRaw.Le z.val.imagPart (RealRaw.ofRat a)) :
    RealRaw.Le (integerShiftScalar z k).val.imagPart (RealRaw.ofRat a) := by
  intro n m
  have h := ha n m
  simpa only [integerShiftScalar,integerAffine,translate,scaleRat,QBox.scaleRat,imagPart,
    add,ofQComplex,QBox.add,QComplex.add,Rat.intCast_one,
    if_pos (show (0:Rat)≤1 by decide),Rat.one_mul,Rat.add_zero] using h

theorem stripRepresentative_middle_band_small (z : Scalar)
    (hlo : RealRaw.Le (RealRaw.ofRat (-2)) z.val.imagPart)
    (hup : RealRaw.Le z.val.imagPart (RealRaw.ofRat 2)) : Small (stripRepresentative z).val 2 :=
  exactMiddleStrip_small (stripRepresentative z) (stripRepresentative_real_bounds z).1
    (stripRepresentative_real_bounds z).2
    (integerShiftScalar_imaginary_lower_bound z (stripTranslation z) (-2) hlo)
    (integerShiftScalar_imaginary_upper_bound z (stripTranslation z) 2 hup)

theorem pairedEntireRiccatiMap_middle_bound_of_small_bound (C : Rat)
    (hb : ∀ w : Scalar, Small w.val 2 → Small (pairedEntireRiccatiMap.eval w trivial).val C)
    (z : Scalar) (hlo : RealRaw.Le (RealRaw.ofRat (-2)) z.val.imagPart)
    (hup : RealRaw.Le z.val.imagPart (RealRaw.ofRat 2)) :
    Small (pairedEntireRiccatiMap.eval z trivial).val C :=
  Small.congr (pairedEntireRiccatiMap.eval (stripRepresentative z) trivial).property
    (pairedEntireRiccatiMap.eval z trivial).property (pairedEntireRiccatiMap_strip_agreement z)
    (hb (stripRepresentative z) (stripRepresentative_middle_band_small z hlo hup))

end ComputableAnalysis.ModularForms
