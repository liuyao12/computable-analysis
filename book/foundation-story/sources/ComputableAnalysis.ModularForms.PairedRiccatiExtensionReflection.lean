import ComputableAnalysis.ModularForms.PairedDivisionDerivativeSumReflection
import ComputableAnalysis.ModularForms.PairedLaurentReflection
import ComputableAnalysis.ModularForms.PairedRiccatiExtensionHolomorphic

/-! Exact even reflection symmetry of the actual local Riccati extension. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedRiccatiExtension_even (z w : Scalar)
    (hz : LocalODE.interior (1/4) z) (hw : LocalODE.interior (1/4) w)
    (he : w.val.Equiv (neg z.val)) :
    (pairedRiccatiExtension w hw).val.Equiv (pairedRiccatiExtension z hz).val := by
  have ht := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedRegularDivisionMap.eval w hw).property)
    (hright := (pairedRegularDivisionMap.eval z hz).property)
    (pairedRegularDivisionValue_even z w (LocalODE.interior_bound _ z hz)
      (LocalODE.interior_bound _ w hw) he)
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedRegularDivisionDerivative w hw).property)
    (hright := neg_valid (pairedRegularDivisionDerivative z hz).property)
    (pairedRegularDivisionDerivativeValue_odd z w hz hw he)
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedRegularPartMap.eval w hw).property)
    (hright := neg_valid (pairedRegularPartMap.eval z hz).property)
    (pairedRegularPart_odd z w (LocalODE.interior_bound _ z hz)
      (LocalODE.interior_bound _ w hw) he)
  have hzD := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedRegularPartDerivative z hz).property)
    (hright := add_valid (pairedRegularDivisionMap.eval z hz).property
      (mul_valid z.property (pairedRegularDivisionDerivative z hz).property))
    (pairedRegularPartDerivative_division z hz)
  have hwD := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedRegularPartDerivative w hw).property)
    (hright := add_valid (pairedRegularDivisionMap.eval w hw).property
      (mul_valid w.property (pairedRegularDivisionDerivative w hw).property))
    (pairedRegularPartDerivative_division w hw)
  have hzw := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := w.property) (hright := neg_valid z.property) he
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedRiccatiExtension w hw).property) (hright := (pairedRiccatiExtension z hz).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let W := ComplexRawQuotient.ofRaw w.val w.property
  let T := ComplexRawQuotient.ofRaw (pairedRegularDivisionMap.eval z hz).val (pairedRegularDivisionMap.eval z hz).property
  let U := ComplexRawQuotient.ofRaw (pairedRegularDivisionMap.eval w hw).val (pairedRegularDivisionMap.eval w hw).property
  let D := ComplexRawQuotient.ofRaw (pairedRegularDivisionDerivative z hz).val (pairedRegularDivisionDerivative z hz).property
  let E := ComplexRawQuotient.ofRaw (pairedRegularDivisionDerivative w hw).val (pairedRegularDivisionDerivative w hw).property
  let S := ComplexRawQuotient.ofRaw (pairedRegularPartMap.eval z hz).val (pairedRegularPartMap.eval z hz).property
  let V := ComplexRawQuotient.ofRaw (pairedRegularPartMap.eval w hw).val (pairedRegularPartMap.eval w hw).property
  let SD := ComplexRawQuotient.ofRaw (pairedRegularPartDerivative z hz).val (pairedRegularPartDerivative z hz).property
  let VD := ComplexRawQuotient.ofRaw (pairedRegularPartDerivative w hw).val (pairedRegularPartDerivative w hw).property
  change U=T at ht
  change E= -D at hd
  change V= -S at hs
  change SD=T+Z*D at hzD
  change VD=U+W*E at hwD
  change W= -Z at hzw
  change VD+((U+U)+V*V)=SD+((T+T)+S*S)
  grind only

end ComputableAnalysis.ModularForms
