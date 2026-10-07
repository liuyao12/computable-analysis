import ComputableAnalysis.ModularForms.PairedRegularDivisionHolomorphic
import ComputableAnalysis.ModularForms.PairedRiccatiExtensionContinuity

/-! Exact differentiated multiplication bridge for regular division. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedRegularPartDerivative_division (z : Scalar) (hz : LocalODE.interior (1/4) z) :
    (pairedRegularPartDerivative z hz).val.Equiv
      (add (pairedRegularDivisionMap.eval z hz).val
        (mul z.val (pairedRegularDivisionDerivative z hz).val)) := by
  let id := affine ⟨zero,ofQComplex_valid _⟩ ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩
  let hid := affine_holomorphic ⟨zero,ofQComplex_valid _⟩ ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩
  let hprod := pairedRegularDivisionMap_holomorphic.productOn hid (fun _ _ => trivial)
  let hnew : Holomorphic pairedRegularPartMap := hprod.transfer pairedRegularPartMap
    (fun _ hz => hz) ⟨LocalODE.interiorRadius (1/4),LocalODE.interiorRadius_inside (1/4)⟩ (by
      intro a ha
      have he := pairedRegularDivisionValue_product a (LocalODE.interior_bound _ a ha)
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := ((productOn pairedRegularDivisionMap id (fun _ _ => trivial)).eval a ha).property)
        (hright := (pairedRegularPartMap.eval a ha).property)
      have h := ComplexRawQuotient.ofRaw_eq_ofRaw
        (hleft := mul_valid a.property (pairedRegularDivisionMap.eval a ha).property)
        (hright := (pairedRegularPartMap.eval a ha).property) he
      let A := ComplexRawQuotient.ofRaw a.val a.property
      let T := ComplexRawQuotient.ofRaw (pairedRegularDivisionMap.eval a ha).val (pairedRegularDivisionMap.eval a ha).property
      let S := ComplexRawQuotient.ofRaw (pairedRegularPartMap.eval a ha).val (pairedRegularPartMap.eval a ha).property
      change A*T=S at h
      change T*(0+1*A)=S
      grind only)
  have he := pairedRegularPartMap_holomorphic.derivative_unique hnew z hz
  apply equiv_trans (pairedRegularPartDerivative z hz).property (hnew.derivative z hz).property
    (add_valid (pairedRegularDivisionMap.eval z hz).property
      (mul_valid z.property (pairedRegularDivisionDerivative z hz).property)) he
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (hnew.derivative z hz).property)
    (hright := add_valid (pairedRegularDivisionMap.eval z hz).property
      (mul_valid z.property (pairedRegularDivisionDerivative z hz).property))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let T := ComplexRawQuotient.ofRaw (pairedRegularDivisionMap.eval z hz).val (pairedRegularDivisionMap.eval z hz).property
  let D := ComplexRawQuotient.ofRaw (pairedRegularDivisionDerivative z hz).val (pairedRegularDivisionDerivative z hz).property
  change D*(0+1*Z)+T*1=T+Z*D
  grind only

theorem pairedRiccatiExtension_at_zero (z : Scalar) (hz : LocalODE.interior (1/4) z)
    (he : z.val.Equiv zero) :
    (pairedRiccatiExtension z hz).val.Equiv
      (add (pairedRegularDivisionMap.eval z hz).val
        (add (pairedRegularDivisionMap.eval z hz).val (pairedRegularDivisionMap.eval z hz).val)) := by
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedRegularPartDerivative z hz).property)
    (hright := add_valid (pairedRegularDivisionMap.eval z hz).property
      (mul_valid z.property (pairedRegularDivisionDerivative z hz).property))
    (pairedRegularPartDerivative_division z hz)
  have hzq := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := z.property) (hright := ofQComplex_valid _) he
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := (pairedRegularPartMap.eval z hz).property)
    (hright := ofQComplex_valid _) (pairedRegularPart_zero z (LocalODE.interior_bound _ z hz) he)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedRiccatiExtension z hz).property)
    (hright := add_valid (pairedRegularDivisionMap.eval z hz).property
      (add_valid (pairedRegularDivisionMap.eval z hz).property (pairedRegularDivisionMap.eval z hz).property))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let S := ComplexRawQuotient.ofRaw (pairedRegularPartMap.eval z hz).val (pairedRegularPartMap.eval z hz).property
  let T := ComplexRawQuotient.ofRaw (pairedRegularDivisionMap.eval z hz).val (pairedRegularDivisionMap.eval z hz).property
  let D := ComplexRawQuotient.ofRaw (pairedRegularDivisionDerivative z hz).val (pairedRegularDivisionDerivative z hz).property
  let SD := ComplexRawQuotient.ofRaw (pairedRegularPartDerivative z hz).val (pairedRegularPartDerivative z hz).property
  change SD=T+Z*D at hd
  change Z=0 at hzq
  change S=0 at hs
  change SD+((T+T)+S*S)=T+(T+T)
  grind only

end ComputableAnalysis.ModularForms
