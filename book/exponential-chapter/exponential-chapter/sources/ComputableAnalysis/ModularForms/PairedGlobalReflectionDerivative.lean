import ComputableAnalysis.ModularForms.PairedGlobalReflectionValue
import ComputableAnalysis.ModularForms.PairedGlobalOffPoleDerivativePeriodicity

/-! Even reflection of the actual global derivative, proved by derivative uniqueness. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedGlobalOffPoleAssemblyMap_derivative_reflection (z : Scalar) (hz : pairedOffPoleDomain z) :
    (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative (pairedReflectionMap.eval z trivial)
      (pairedOffPoleDomain_reflection z hz)).val.Equiv
      (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z hz).val := by
  let hf := pairedGlobalOffPoleAssemblyMap_holomorphic
  let ht : Holomorphic (negate pairedGlobalOffPoleAssemblyMap) :=
    (hf.compose pairedReflectionMap_holomorphic).transfer (negate pairedGlobalOffPoleAssemblyMap)
      (fun z hz => ⟨trivial,pairedOffPoleDomain_reflection z hz⟩)
      hf.negate.openDomain (fun z hz => globalOffPoleValue_reflection z hz)
  have hi := ht.derivative_unique hf.negate z hz
  have hiq := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := (ht.derivative z hz).property)
    (hright := (hf.negate.derivative z hz).property) hi
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (hf.derivative (pairedReflectionMap.eval z trivial) (pairedOffPoleDomain_reflection z hz)).property)
    (hright := (hf.derivative z hz).property)
  let A := ComplexRawQuotient.ofRaw
    (hf.derivative (pairedReflectionMap.eval z trivial) (pairedOffPoleDomain_reflection z hz)).val
    (hf.derivative (pairedReflectionMap.eval z trivial) (pairedOffPoleDomain_reflection z hz)).property
  let D := ComplexRawQuotient.ofRaw (hf.derivative z hz).val (hf.derivative z hz).property
  change A*ComplexRawQuotient.ofQComplex ⟨(-1:Rat),0⟩= -D at hiq
  have hm : ComplexRawQuotient.ofQComplex ⟨(-1:Rat),0⟩ = ((-1:Int):ComplexRawQuotient.Value) := by
    simpa only [Rat.intCast_neg,Rat.intCast_one] using integer_constant (-1:Int)
  rw [hm] at hiq
  change A=D
  grind only

theorem pairedGlobalOffPoleRiccatiMap_reflection (z : Scalar) (hz : pairedOffPoleDomain z) :
    (pairedGlobalOffPoleRiccatiMap.eval (pairedReflectionMap.eval z trivial)
      (pairedOffPoleDomain_reflection z hz)).val.Equiv
      (pairedGlobalOffPoleRiccatiMap.eval z hz).val := by
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := globalOffPoleValue_valid _ (pairedOffPoleDomain_reflection z hz))
    (hright := neg_valid (globalOffPoleValue_valid z hz)) (globalOffPoleValue_reflection z hz)
  rw [ComplexRawQuotient.ofRaw_neg _ (globalOffPoleValue_valid z hz)] at hp
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative
      (pairedReflectionMap.eval z trivial) (pairedOffPoleDomain_reflection z hz)).property)
    (hright := (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z hz).property)
    (pairedGlobalOffPoleAssemblyMap_derivative_reflection z hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedGlobalOffPoleRiccatiMap.eval (pairedReflectionMap.eval z trivial)
      (pairedOffPoleDomain_reflection z hz)).property)
    (hright := (pairedGlobalOffPoleRiccatiMap.eval z hz).property)
  let P := ComplexRawQuotient.ofRaw (globalOffPoleValue z hz) (globalOffPoleValue_valid z hz)
  let Q := ComplexRawQuotient.ofRaw (globalOffPoleValue (pairedReflectionMap.eval z trivial)
    (pairedOffPoleDomain_reflection z hz)) (globalOffPoleValue_valid _ (pairedOffPoleDomain_reflection z hz))
  let D := ComplexRawQuotient.ofRaw (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z hz).val
    (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z hz).property
  let E := ComplexRawQuotient.ofRaw (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative
    (pairedReflectionMap.eval z trivial) (pairedOffPoleDomain_reflection z hz)).val
    (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative
      (pairedReflectionMap.eval z trivial) (pairedOffPoleDomain_reflection z hz)).property
  change Q= -P at hp
  change E=D at hd
  change E+Q*Q=D+P*P
  grind only

end ComputableAnalysis.ModularForms
