import ComputableAnalysis.ModularForms.LatticeHalfPeriodZero
import ComputableAnalysis.ModularForms.PairedRiccatiConstantSeparation

/-! The actual lattice half-period zero has a proved nonzero derivative. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem latticeHalfPeriod_mem (z : Scalar) (he : z.val.Equiv latticeHalfPoint.val) :
    pairedOffPoleDomain z :=
  (pairedOffPoleDomain_congr z latticeHalfPoint he).mpr latticeHalfPoint_mem

theorem latticeHalfPeriod_value_zero (z : Scalar) (he : z.val.Equiv latticeHalfPoint.val) :
    (pairedGlobalOffPoleAssemblyMap.eval z (latticeHalfPeriod_mem z he)).val.Equiv zero :=
  equiv_trans (pairedGlobalOffPoleAssemblyMap.eval z (latticeHalfPeriod_mem z he)).property
    (globalOffPoleValue_valid latticeHalfPoint latticeHalfPoint_mem) (ofQComplex_valid _)
    (pairedGlobalOffPoleAssemblyMap.eval_congr z latticeHalfPoint _ _ he)
    globalOffPoleValue_halfPeriod_zero

theorem latticeHalfPeriod_derivative (z : Scalar) (he : z.val.Equiv latticeHalfPoint.val) :
    (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z (latticeHalfPeriod_mem z he)).val.Equiv
      pairedRiccatiCenterConstant.val := by
  let hz := latticeHalfPeriod_mem z he
  let p := pairedGlobalOffPoleAssemblyMap.eval z hz
  let d := pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z hz
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := p.property) (hright := ofQComplex_valid _)
    (latticeHalfPeriod_value_zero z he)
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := add_valid d.property (mul_valid p.property p.property))
    (hright := pairedRiccatiCenterConstant.property)
    (pairedGlobalOffPoleAssemblyMap_riccati_identity z hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := d.property)
    (hright := pairedRiccatiCenterConstant.property)
  let P := gridScalarValue p
  let D := gridScalarValue d
  let C := gridScalarValue pairedRiccatiCenterConstant
  change P=0 at hp
  change D+P*P=C at hd
  change D=C
  rw [hp] at hd
  grind only

theorem latticeHalfPeriod_derivative_nonzero (z : Scalar) (he : z.val.Equiv latticeHalfPoint.val) :
    NonzeroBoxSearch.Nonzero
      (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z (latticeHalfPeriod_mem z he)) :=
  (NonzeroBoxSearch.nonzero_congr _ _ (latticeHalfPeriod_derivative z he)).mpr
    pairedRiccatiCenterConstant_nonzero

end ComputableAnalysis.ModularForms
