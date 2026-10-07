import ComputableAnalysis.ModularForms.PairedGlobalOffPoleIntegerPeriodicity

/-! Integer translation laws for actual derivatives and the global Riccati map. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem holomorphic_integer_translation_derivative {f : DomainFunctions.Map} (hf : Holomorphic f)
    (k : Int) (mem : ∀ z, f.domain z → f.domain (integerShiftScalar z k))
    (period : ∀ z hz, (f.eval (integerShiftScalar z k) (mem z hz)).val.Equiv (f.eval z hz).val)
    (z : Scalar) (hz : f.domain z) :
    (hf.derivative (integerShiftScalar z k) (mem z hz)).val.Equiv (hf.derivative z hz).val := by
  let ht : Holomorphic f := (hf.compose (entireIntegerShiftMap_holomorphic k)).transfer f
    (fun z hz => ⟨trivial,mem z hz⟩) hf.openDomain period
  have hi := ht.derivative_unique hf z hz
  have hd : (ht.derivative z hz).val.Equiv (hf.derivative (integerShiftScalar z k) (mem z hz)).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (ht.derivative z hz).property)
      (hright := (hf.derivative (integerShiftScalar z k) (mem z hz)).property)
    let X := ComplexRawQuotient.ofRaw (hf.derivative (integerShiftScalar z k) (mem z hz)).val
      (hf.derivative (integerShiftScalar z k) (mem z hz)).property
    change X*ComplexRawQuotient.ofQComplex ⟨((1:Int):Rat),0⟩=X
    rw [integer_constant]
    grind only
  exact equiv_trans (hf.derivative (integerShiftScalar z k) (mem z hz)).property
    (ht.derivative z hz).property (hf.derivative z hz).property (equiv_symm hd) hi

theorem pairedGlobalOffPoleAssemblyMap_derivative_period_int (k : Int) (z : Scalar)
    (hz : pairedOffPoleDomain z) :
    (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative (integerShiftScalar z k)
      (pairedOffPoleDomain_shift z hz k)).val.Equiv
      (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z hz).val :=
  holomorphic_integer_translation_derivative pairedGlobalOffPoleAssemblyMap_holomorphic k
    (fun z hz => pairedOffPoleDomain_shift z hz k) (fun z hz => globalOffPoleValue_period_int z hz k) z hz

theorem pairedGlobalOffPoleAssemblyMap_secondDerivative_period_int (k : Int) (z : Scalar)
    (hz : pairedOffPoleDomain z) :
    (pairedGlobalOffPoleAssemblyMap_derivative_holomorphic.derivative (integerShiftScalar z k)
      (pairedOffPoleDomain_shift z hz k)).val.Equiv
      (pairedGlobalOffPoleAssemblyMap_derivative_holomorphic.derivative z hz).val :=
  holomorphic_integer_translation_derivative pairedGlobalOffPoleAssemblyMap_derivative_holomorphic k
    (fun z hz => pairedOffPoleDomain_shift z hz k)
    (fun z hz => pairedGlobalOffPoleAssemblyMap_derivative_period_int k z hz) z hz

theorem pairedGlobalOffPoleRiccatiMap_period_int (k : Int) (z : Scalar) (hz : pairedOffPoleDomain z) :
    (pairedGlobalOffPoleRiccatiMap.eval (integerShiftScalar z k) (pairedOffPoleDomain_shift z hz k)).val.Equiv
      (pairedGlobalOffPoleRiccatiMap.eval z hz).val := by
  have hp := globalOffPoleValue_period_int z hz k
  exact add_equiv (pairedGlobalOffPoleAssemblyMap_derivative_period_int k z hz)
    (mul_equiv (pairedGlobalOffPoleAssemblyMap.eval (integerShiftScalar z k) (pairedOffPoleDomain_shift z hz k)).property
      (pairedGlobalOffPoleAssemblyMap.eval z hz).property
      (pairedGlobalOffPoleAssemblyMap.eval (integerShiftScalar z k) (pairedOffPoleDomain_shift z hz k)).property
      (pairedGlobalOffPoleAssemblyMap.eval z hz).property hp hp)

theorem pairedGlobalOffPoleRiccatiMap_derivative_period_int (k : Int) (z : Scalar) (hz : pairedOffPoleDomain z) :
    (pairedGlobalOffPoleRiccatiMap_holomorphic.derivative (integerShiftScalar z k)
      (pairedOffPoleDomain_shift z hz k)).val.Equiv
      (pairedGlobalOffPoleRiccatiMap_holomorphic.derivative z hz).val :=
  holomorphic_integer_translation_derivative pairedGlobalOffPoleRiccatiMap_holomorphic k
    (fun z hz => pairedOffPoleDomain_shift z hz k) (fun z hz => pairedGlobalOffPoleRiccatiMap_period_int k z hz) z hz

end ComputableAnalysis.ModularForms
