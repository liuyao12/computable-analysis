import ComputableAnalysis.ModularForms.PairedRiccatiPoleDerivativeBound

/-! Uniform entire Riccati derivative control on the fixed represented box. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedIntegerRiccatiExtensionMap_derivative_uniform_bound (k : Int) (z : Scalar)
    (hz : (pairedIntegerRiccatiExtensionMap k).domain z) :
    Small ((pairedIntegerRiccatiExtensionMap_holomorphic k).derivative z hz).val 4352 := by
  let w := integerShiftScalar z (-k)
  have hw := compose_outer_mem hz
  have he : ((pairedIntegerRiccatiExtensionMap_holomorphic k).derivative z hz).val.Equiv
      (pairedRiccatiExtensionMap_holomorphic.derivative w hw).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((pairedIntegerRiccatiExtensionMap_holomorphic k).derivative z hz).property)
      (hright := (pairedRiccatiExtensionMap_holomorphic.derivative w hw).property)
    let D := ComplexRawQuotient.ofRaw (pairedRiccatiExtensionMap_holomorphic.derivative w hw).val
      (pairedRiccatiExtensionMap_holomorphic.derivative w hw).property
    change D*ComplexRawQuotient.ofQComplex ⟨(1:Rat),0⟩=D
    have ho : ComplexRawQuotient.ofQComplex ⟨(1:Rat),0⟩ = ((1:Int):ComplexRawQuotient.Value) := by
      simpa only [Rat.intCast_one] using integer_constant (1:Int)
    rw [ho]
    grind only
  exact Small.congr (pairedRiccatiExtensionMap_holomorphic.derivative w hw).property
    ((pairedIntegerRiccatiExtensionMap_holomorphic k).derivative z hz).property (equiv_symm he)
    (pairedRiccatiExtensionMap_derivative_uniform_bound w hw)

theorem pairedEntireRiccatiMap_integer_derivative_bound (k : Int) (z : Scalar)
    (hz : (pairedIntegerRiccatiExtensionMap k).domain z) :
    Small (pairedEntireRiccatiMap_holomorphic.derivative z trivial).val 4352 :=
  Small.congr ((pairedIntegerRiccatiExtensionMap_holomorphic k).derivative z hz).property
    (pairedEntireRiccatiMap_holomorphic.derivative z trivial).property
    (pairedEntireRiccatiMap_chart_derivative_agreement (.pole k) z hz)
    (pairedIntegerRiccatiExtensionMap_derivative_uniform_bound k z hz)

theorem pairedEntireRiccatiMap_fixed_box_derivative_bound (z : Scalar) (hs : Small z.val 2) :
    Small (pairedEntireRiccatiMap_holomorphic.derivative z trivial).val 1427432192 := by
  classical
  by_cases hp : ∃ k : Int, (pairedIntegerRiccatiExtensionMap k).domain z
  · obtain ⟨k,hk⟩ := hp
    exact (pairedEntireRiccatiMap_integer_derivative_bound k z hk).mono (by decide +kernel)
  · exact pairedEntireRiccatiMap_fixed_box_derivative_outside_charts_bound z hs hp

theorem pairedEntireRiccatiMap_middle_band_derivative_bound (z : Scalar)
    (hlo : RealRaw.Le (RealRaw.ofRat (-2)) z.val.imagPart)
    (hup : RealRaw.Le z.val.imagPart (RealRaw.ofRat 2)) :
    Small (pairedEntireRiccatiMap_holomorphic.derivative z trivial).val 1427432192 :=
  Small.congr (pairedEntireRiccatiMap_holomorphic.derivative (stripRepresentative z) trivial).property
    (pairedEntireRiccatiMap_holomorphic.derivative z trivial).property
    (pairedEntireRiccatiMap_derivative_period_int (stripTranslation z) z)
    (pairedEntireRiccatiMap_fixed_box_derivative_bound (stripRepresentative z)
      (stripRepresentative_middle_band_small z hlo hup))

end ComputableAnalysis.ModularForms
