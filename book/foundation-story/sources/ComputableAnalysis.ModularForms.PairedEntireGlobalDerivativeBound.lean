import ComputableAnalysis.ModularForms.PairedEntireUpperDerivativeBound

/-! Whole-plane derivative control for the actual entire Riccati map. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedEntireRiccatiMap_derivative_reflection (z : Scalar) :
    (pairedEntireRiccatiMap_holomorphic.derivative (pairedReflectionMap.eval z trivial) trivial).val.Equiv
      (neg (pairedEntireRiccatiMap_holomorphic.derivative z trivial).val) := by
  let hf := pairedEntireRiccatiMap_holomorphic
  let ht : Holomorphic pairedEntireRiccatiMap :=
    (hf.compose pairedReflectionMap_holomorphic).transfer pairedEntireRiccatiMap
      (fun _ _ => ⟨trivial,trivial⟩) hf.openDomain
      (fun z _ => pairedEntireRiccatiMap_reflection z)
  have hi := ht.derivative_unique hf z trivial
  have hiq := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := (ht.derivative z trivial).property)
    (hright := (hf.derivative z trivial).property) hi
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (hf.derivative (pairedReflectionMap.eval z trivial) trivial).property)
    (hright := neg_valid (hf.derivative z trivial).property)
  rw [ComplexRawQuotient.ofRaw_neg _ (hf.derivative z trivial).property]
  let A := ComplexRawQuotient.ofRaw (hf.derivative (pairedReflectionMap.eval z trivial) trivial).val
    (hf.derivative (pairedReflectionMap.eval z trivial) trivial).property
  let D := ComplexRawQuotient.ofRaw (hf.derivative z trivial).val (hf.derivative z trivial).property
  change A*ComplexRawQuotient.ofQComplex ⟨(-1:Rat),0⟩=D at hiq
  have hm : ComplexRawQuotient.ofQComplex ⟨(-1:Rat),0⟩=((-1:Int):ComplexRawQuotient.Value) := by
    simpa only [Rat.intCast_neg,Rat.intCast_one] using integer_constant (-1:Int)
  rw [hm] at hiq
  change A= -D
  grind only

theorem pairedEntireRiccatiMap_below_minus_two_derivative_bound (z : Scalar)
    (him : RealRaw.Le z.val.imagPart (RealRaw.ofRat (-2))) :
    Small (pairedEntireRiccatiMap_holomorphic.derivative z trivial).val 6764544 := by
  have hb := pairedEntireRiccatiMap_above_two_derivative_bound (pairedReflectionMap.eval z trivial)
    (pairedReflection_imaginary_below_two z him)
  have hn := Small.congr
    (pairedEntireRiccatiMap_holomorphic.derivative (pairedReflectionMap.eval z trivial) trivial).property
    (neg_valid (pairedEntireRiccatiMap_holomorphic.derivative z trivial).property)
    (pairedEntireRiccatiMap_derivative_reflection z) hb
  have he : (neg (neg (pairedEntireRiccatiMap_holomorphic.derivative z trivial).val)).Equiv
      (pairedEntireRiccatiMap_holomorphic.derivative z trivial).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (neg_valid (pairedEntireRiccatiMap_holomorphic.derivative z trivial).property))
      (hright := (pairedEntireRiccatiMap_holomorphic.derivative z trivial).property)
    rw [ComplexRawQuotient.ofRaw_neg _ (neg_valid (pairedEntireRiccatiMap_holomorphic.derivative z trivial).property),
      ComplexRawQuotient.ofRaw_neg _ (pairedEntireRiccatiMap_holomorphic.derivative z trivial).property]
    grind only
  exact Small.congr
    (neg_valid (neg_valid (pairedEntireRiccatiMap_holomorphic.derivative z trivial).property))
    (pairedEntireRiccatiMap_holomorphic.derivative z trivial).property he (SeriesLimitLaws.small_neg hn)

theorem pairedEntireRiccatiMap_global_derivative_bound (z : Scalar) :
    Small (pairedEntireRiccatiMap_holomorphic.derivative z trivial).val 1427432192 := by
  rcases representedReal_le_total z.val.imagPart (RealRaw.ofRat (-2))
    (imagPart_valid z.property) (RealRaw.ofRat_valid _) with hlo | hlo
  · exact (pairedEntireRiccatiMap_below_minus_two_derivative_bound z hlo).mono (by decide +kernel)
  · rcases representedReal_le_total z.val.imagPart (RealRaw.ofRat 2)
      (imagPart_valid z.property) (RealRaw.ofRat_valid _) with hup | hup
    · exact pairedEntireRiccatiMap_middle_band_derivative_bound z hlo hup
    · exact (pairedEntireRiccatiMap_above_two_derivative_bound z hup).mono (by decide +kernel)

end ComputableAnalysis.ModularForms
