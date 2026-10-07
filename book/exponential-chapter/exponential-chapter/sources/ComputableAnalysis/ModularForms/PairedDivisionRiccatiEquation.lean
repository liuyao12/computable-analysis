import ComputableAnalysis.ModularForms.PairedDivisionQuadraticDerivative
import ComputableAnalysis.ModularForms.PairedEntireRiccatiConstancy

/-! Exact regular-division Riccati equation on the open quarter chart. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

/-- The actual local Riccati extension has the globally proved constant value. -/
theorem pairedRiccatiExtension_constant (z : Scalar) (hz : LocalODE.interior (1/4) z) :
    (pairedRiccatiExtension z hz).val.Equiv pairedRiccatiCenterConstant.val := by
  let w := integerShiftScalar z 0
  have he : w.val.Equiv z.val := integerShiftScalar_zero_equiv z
  have hw : LocalODE.interior (1/4) w :=
    (pairedRiccatiExtensionMap.domain_congr z w (equiv_symm he)).mp hz
  have hi : (pairedIntegerRiccatiExtensionMap 0).domain z := ⟨trivial,hw⟩
  have hchart := pairedEntireRiccatiMap_chart_agreement (.pole 0) z hi
  have hconst := pairedEntireRiccatiMap_center_identity z
  have hlocal : ((pairedIntegerRiccatiExtensionMap 0).eval z hi).val.Equiv (pairedRiccatiExtension z hz).val :=
    pairedRiccatiExtension_congr w z hw hz he
  exact equiv_trans (pairedRiccatiExtension z hz).property
    ((pairedIntegerRiccatiExtensionMap 0).eval z hi).property pairedRiccatiCenterConstant.property
    (equiv_symm hlocal)
    (equiv_trans ((pairedIntegerRiccatiExtensionMap 0).eval z hi).property
      (pairedEntireRiccatiMap.eval z trivial).property pairedRiccatiCenterConstant.property hchart hconst)

/-- Exact differential equation for the actual division value, including the center. -/
theorem pairedRegularDivision_riccati_identity (z : Scalar) (hz : LocalODE.interior (1/4) z) :
    (add (mul z.val (pairedRegularDivisionDerivative z hz).val)
      (add (pairedRegularDivisionMap.eval z hz).val
        (add (pairedRegularDivisionMap.eval z hz).val
          (add (pairedRegularDivisionMap.eval z hz).val
            (mul (mul z.val z.val)
              (mul (pairedRegularDivisionMap.eval z hz).val (pairedRegularDivisionMap.eval z hz).val)))))).Equiv
      pairedRiccatiCenterConstant.val := by
  let q := pairedRegularDivisionMap.eval z hz
  let d := pairedRegularDivisionDerivative z hz
  let s := pairedRegularPartMap.eval z hz
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property q.property) (hright := s.property)
    (pairedRegularDivisionValue_product z (LocalODE.interior_bound _ z hz))
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedRegularPartDerivative z hz).property)
    (hright := add_valid q.property (mul_valid z.property d.property))
    (pairedRegularPartDerivative_division z hz)
  have vexpr := add_valid (mul_valid z.property d.property)
    (add_valid q.property (add_valid q.property
      (add_valid q.property (mul_valid (mul_valid z.property z.property) (mul_valid q.property q.property)))))
  have he : (add (mul z.val d.val) (add q.val (add q.val (add q.val
      (mul (mul z.val z.val) (mul q.val q.val)))))).Equiv (pairedRiccatiExtension z hz).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := vexpr) (hright := (pairedRiccatiExtension z hz).property)
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    let Q := ComplexRawQuotient.ofRaw q.val q.property
    let D := ComplexRawQuotient.ofRaw d.val d.property
    let S := ComplexRawQuotient.ofRaw s.val s.property
    let E := ComplexRawQuotient.ofRaw (pairedRegularPartDerivative z hz).val (pairedRegularPartDerivative z hz).property
    change Z*Q=S at hp
    change E=Q+Z*D at hd
    change Z*D+(Q+(Q+(Q+(Z*Z)*(Q*Q))))=E+((Q+Q)+S*S)
    generalize Z=z,Q=q,D=d,S=s,E=e at hp hd ⊢
    grind only
  exact equiv_trans vexpr (pairedRiccatiExtension z hz).property pairedRiccatiCenterConstant.property
    he (pairedRiccatiExtension_constant z hz)

end ComputableAnalysis.ModularForms
