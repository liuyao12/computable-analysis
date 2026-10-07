import ComputableAnalysis.ModularForms.PairedUpperRiccatiDerivative

/-! Reflected actual Riccati construction on the opposite half-plane. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedReflectionMap : DomainFunctions.Map :=
  affine ⟨zero,ofQComplex_valid _⟩ ⟨ofQComplex ⟨-1,0⟩,ofQComplex_valid _⟩

def pairedReflectionMap_holomorphic : Holomorphic pairedReflectionMap :=
  affine_holomorphic ⟨zero,ofQComplex_valid _⟩ ⟨ofQComplex ⟨-1,0⟩,ofQComplex_valid _⟩

theorem pairedReflectionMap_eval (z : Scalar) :
    (pairedReflectionMap.eval z trivial).val.Equiv (neg z.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedReflectionMap.eval z trivial).property) (hright := neg_valid z.property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change 0+ComplexRawQuotient.ofQComplex ⟨-1,0⟩*Z= -Z
  have hm : ComplexRawQuotient.ofQComplex ⟨(-1:Rat),0⟩ = ((-1:Int):ComplexRawQuotient.Value) := by
    simpa only [Rat.intCast_neg,Rat.intCast_one] using integer_constant (-1:Int)
  rw [hm]
  grind only

def pairedReflectedRiccatiMap : DomainFunctions.Map :=
  compose pairedUpperRiccatiMap pairedReflectionMap


theorem pairedReflectedRiccatiMap_domain (z : Scalar) :
    pairedReflectedRiccatiMap.domain z ↔ InUpperHalfPlane (neg z.val) := by
  have he := upperHalfPlane_congr (pairedReflectionMap.eval z trivial).property
    (neg_valid z.property) (pairedReflectionMap_eval z)
  constructor
  · intro hz
    exact he.mp (compose_outer_mem hz)
  · intro hz
    exact ⟨trivial,he.mpr hz⟩

noncomputable def pairedReflectedRiccatiMap_holomorphic : Holomorphic pairedReflectedRiccatiMap :=
  pairedUpperRiccatiMap_holomorphic.compose pairedReflectionMap_holomorphic

theorem pairedReflectedRiccatiMap_derivative (z : Scalar)
    (hz : pairedReflectedRiccatiMap.domain z) :
    (pairedReflectedRiccatiMap_holomorphic.derivative z hz).val.Equiv
      (neg (pairedUpperRiccatiDerivative (pairedReflectionMap.eval z trivial)
        (compose_outer_mem hz)).val) := by
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedUpperRiccatiMap_holomorphic.derivative
      (pairedReflectionMap.eval z trivial) (compose_outer_mem hz)).property)
    (hright := (pairedUpperRiccatiDerivative (pairedReflectionMap.eval z trivial)
      (compose_outer_mem hz)).property)
    (pairedUpperRiccatiMap_derivative _ _)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedReflectedRiccatiMap_holomorphic.derivative z hz).property)
    (hright := neg_valid (pairedUpperRiccatiDerivative (pairedReflectionMap.eval z trivial)
      (compose_outer_mem hz)).property)
  let D := ComplexRawQuotient.ofRaw (pairedUpperRiccatiMap_holomorphic.derivative
    (pairedReflectionMap.eval z trivial) (compose_outer_mem hz)).val
    (pairedUpperRiccatiMap_holomorphic.derivative _ _).property
  let E := ComplexRawQuotient.ofRaw (pairedUpperRiccatiDerivative
    (pairedReflectionMap.eval z trivial) (compose_outer_mem hz)).val
    (pairedUpperRiccatiDerivative _ _).property
  change D=E at hd
  change D*ComplexRawQuotient.ofQComplex ⟨-1,0⟩= -E
  have hm : ComplexRawQuotient.ofQComplex ⟨(-1:Rat),0⟩ = ((-1:Int):ComplexRawQuotient.Value) := by
    simpa only [Rat.intCast_neg,Rat.intCast_one] using integer_constant (-1:Int)
  rw [hm]
  grind only

end ComputableAnalysis.ModularForms
