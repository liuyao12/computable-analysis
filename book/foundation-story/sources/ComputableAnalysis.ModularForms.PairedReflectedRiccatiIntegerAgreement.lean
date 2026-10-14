import ComputableAnalysis.ModularForms.PairedReflectedRiccatiExtensionAgreement
import ComputableAnalysis.ModularForms.PairedUpperRiccatiIntegerAgreement

/-! Reflected Riccati agreement with every integer pole extension. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedReflection_integerShift (z : Scalar) (k : Int) :
    (pairedReflectionMap.eval (integerShiftScalar z k) trivial).val.Equiv
      (integerShiftScalar (pairedReflectionMap.eval z trivial) (-k)).val := by
  have hz := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedReflectionMap.eval z trivial).property) (hright := neg_valid z.property)
    (pairedReflectionMap_eval z)
  have hw := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedReflectionMap.eval (integerShiftScalar z k) trivial).property)
    (hright := neg_valid (integerShiftScalar z k).property)
    (pairedReflectionMap_eval (integerShiftScalar z k))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedReflectionMap.eval (integerShiftScalar z k) trivial).property)
    (hright := (integerShiftScalar (pairedReflectionMap.eval z trivial) (-k)).property)
  rw [ComplexRawQuotient.ofRaw_neg _ (integerShiftScalar z k).property] at hw
  simp only [integerShiftScalar,integerAffine_class] at hw ⊢
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let R := ComplexRawQuotient.ofRaw (pairedReflectionMap.eval z trivial).val (pairedReflectionMap.eval z trivial).property
  change R= -Z at hz
  grind only

theorem pairedReflectedRiccati_integerShift_domain (z : Scalar)
    (hz : pairedReflectedRiccatiMap.domain z) (k : Int) :
    pairedReflectedRiccatiMap.domain (integerShiftScalar z k) := by
  have hupper := integerShiftScalar_upper (pairedReflectionMap.eval z trivial)
    (compose_outer_mem hz) (-k)
  have he := pairedReflection_integerShift z k
  exact ⟨trivial,(upperHalfPlane_congr
    (pairedReflectionMap.eval (integerShiftScalar z k) trivial).property
    (integerShiftScalar (pairedReflectionMap.eval z trivial) (-k)).property he).mpr hupper⟩

theorem pairedReflectedRiccatiValue_period_int (z : Scalar)
    (hz : pairedReflectedRiccatiMap.domain z) (k : Int) :
    (pairedReflectedRiccatiMap.eval (integerShiftScalar z k)
      (pairedReflectedRiccati_integerShift_domain z hz k)).val.Equiv
      (pairedReflectedRiccatiMap.eval z hz).val := by
  have hshift := pairedReflectedRiccati_integerShift_domain z hz k
  have he := pairedUpperRiccatiValue_congr _ _ (compose_outer_mem hshift)
    (integerShiftScalar_upper _ (compose_outer_mem hz) (-k)) (pairedReflection_integerShift z k)
  exact equiv_trans (pairedReflectedRiccatiMap.eval (integerShiftScalar z k) hshift).property
    (pairedUpperRiccatiValue (integerShiftScalar (pairedReflectionMap.eval z trivial) (-k))
      (integerShiftScalar_upper _ (compose_outer_mem hz) (-k))).property
    (pairedReflectedRiccatiMap.eval z hz).property he
    (pairedUpperRiccatiValue_period_int (-k) _ (compose_outer_mem hz))

theorem pairedReflectedRiccati_integer_extension_agreement (k : Int) (z : Scalar)
    (hz : pairedReflectedRiccatiMap.domain z)
    (hq : (pairedIntegerRiccatiExtensionMap k).domain z) :
    (pairedReflectedRiccatiMap.eval z hz).val.Equiv
      ((pairedIntegerRiccatiExtensionMap k).eval z hq).val := by
  let w := integerShiftScalar z (-k)
  have hw := pairedReflectedRiccati_integerShift_domain z hz (-k)
  exact equiv_trans (pairedReflectedRiccatiMap.eval z hz).property
    (pairedReflectedRiccatiMap.eval w hw).property
    ((pairedIntegerRiccatiExtensionMap k).eval z hq).property
    (equiv_symm (pairedReflectedRiccatiValue_period_int z hz (-k)))
    (pairedReflectedRiccati_extension_agreement w hw (compose_outer_mem hq))

end ComputableAnalysis.ModularForms
