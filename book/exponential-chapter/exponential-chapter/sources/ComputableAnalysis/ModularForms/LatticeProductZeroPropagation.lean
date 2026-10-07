import ComputableAnalysis.ModularForms.HomogeneousSegmentZeroPropagation
import ComputableAnalysis.ModularForms.LatticeHalfShiftProductError
import ComputableAnalysis.ModularForms.HomogeneousZeroNeighborhood

/-! Constructed zero propagation neighborhoods for the actual lattice product error. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
noncomputable section
set_option maxHeartbeats 1000000

def latticeProductErrorCoefficientMap : DomainFunctions.Map :=
  negate (intersectionSum pairedGlobalOffPoleAssemblyMap shiftedLatticeKernelMap)

def latticeProductErrorCoefficientMap_holomorphic : Holomorphic latticeProductErrorCoefficientMap :=
  (pairedGlobalOffPoleAssemblyMap_holomorphic.intersectionSum shiftedLatticeKernelMap_holomorphic).negate

theorem latticeProductError_coefficient_mem (z : Scalar)
    (hz : latticeHalfShiftProductErrorMap.domain z) : latticeProductErrorCoefficientMap.domain z :=
  compose_inner_mem (g := latticeHalfShiftProductMap) hz

theorem latticeProductError_coefficient_equation (z : Scalar)
    (hz : latticeHalfShiftProductErrorMap.domain z) :
    (latticeHalfShiftProductErrorMap_holomorphic.derivative z hz).val.Equiv
      (mul (latticeProductErrorCoefficientMap.eval z (latticeProductError_coefficient_mem z hz)).val
        (latticeHalfShiftProductErrorMap.eval z hz).val) := by
  let p := pairedGlobalOffPoleAssemblyMap.eval z (latticeProductError_coefficient_mem z hz).1
  let q := shiftedLatticeKernelMap.eval z (latticeProductError_coefficient_mem z hz).2
  let e := latticeHalfShiftProductErrorMap.eval z hz
  let d := latticeHalfShiftProductErrorMap_holomorphic.derivative z hz
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := d.property)
    (hright := neg_valid (mul_valid (add_valid p.property q.property) e.property))
    (latticeHalfShiftProductError_differential_identity z hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := d.property)
    (hright := mul_valid (latticeProductErrorCoefficientMap.eval z (latticeProductError_coefficient_mem z hz)).property e.property)
  let P := gridScalarValue p
  let Q := gridScalarValue q
  let E := gridScalarValue e
  let D := gridScalarValue d
  change D= -((P+Q)*E) at hd
  change D= -(P+Q)*E
  rw [hd]
  grind only

def latticeProductZeroRadius (a : Scalar) (ha : latticeHalfShiftProductErrorMap.domain a) : QPos :=
  HomogeneousZeroNeighborhood.radius latticeHalfShiftProductErrorMap latticeProductErrorCoefficientMap
    latticeHalfShiftProductErrorMap_holomorphic latticeProductErrorCoefficientMap_holomorphic
    latticeProductError_coefficient_mem a ha

theorem latticeProductZeroNeighborhood_mem (a : Scalar) (ha : latticeHalfShiftProductErrorMap.domain a)
    (z : Scalar) (hz : Small (sub z.val a.val) (latticeProductZeroRadius a ha).val) :
    latticeHalfShiftProductErrorMap.domain z :=
  HomogeneousZeroNeighborhood.mem latticeHalfShiftProductErrorMap latticeProductErrorCoefficientMap
    latticeHalfShiftProductErrorMap_holomorphic latticeProductErrorCoefficientMap_holomorphic
    latticeProductError_coefficient_mem a ha z hz

theorem latticeProductZeroNeighborhood_zero (a : Scalar) (ha : latticeHalfShiftProductErrorMap.domain a)
    (he : (latticeHalfShiftProductErrorMap.eval a ha).val.Equiv zero)
    (z : Scalar) (hz : Small (sub z.val a.val) (latticeProductZeroRadius a ha).val) :
    (latticeHalfShiftProductErrorMap.eval z (latticeProductZeroNeighborhood_mem a ha z hz)).val.Equiv zero :=
  HomogeneousZeroNeighborhood.zero_neighborhood latticeHalfShiftProductErrorMap latticeProductErrorCoefficientMap
    latticeHalfShiftProductErrorMap_holomorphic latticeProductErrorCoefficientMap_holomorphic
    latticeProductError_coefficient_mem a ha latticeProductError_coefficient_equation he z hz

theorem latticeProductError_segment_zero (p q : Scalar)
    (hp : latticeHalfShiftProductErrorMap.domain p) (hq : latticeHalfShiftProductErrorMap.domain q)
    (hdom : ∀ t : UnitInterval.Point,
      latticeHalfShiftProductErrorMap.domain (RepresentedAffineSegment.point p q t))
    (he : (latticeHalfShiftProductErrorMap.eval p hp).val.Equiv zero) :
    (latticeHalfShiftProductErrorMap.eval q hq).val.Equiv zero :=
  homogeneous_segment_zero latticeHalfShiftProductErrorMap latticeProductErrorCoefficientMap
    latticeHalfShiftProductErrorMap_holomorphic latticeProductErrorCoefficientMap_holomorphic
    latticeProductError_coefficient_mem latticeProductError_coefficient_equation p q hp hq hdom he

theorem latticeProductError_segment_product (p q : Scalar)
    (hp : latticeHalfShiftProductErrorMap.domain p) (hq : latticeHalfShiftProductErrorMap.domain q)
    (hdom : ∀ t : UnitInterval.Point,
      latticeHalfShiftProductErrorMap.domain (RepresentedAffineSegment.point p q t))
    (he : (latticeHalfShiftProductErrorMap.eval p hp).val.Equiv zero) :
    (mul (pairedGlobalOffPoleAssemblyMap.eval q (compose_inner_mem hq).1).val
      (shiftedLatticeKernelMap.eval q (compose_inner_mem hq).2).val).Equiv pairedRiccatiCenterConstant.val := by
  have hz := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (latticeHalfShiftProductErrorMap.eval q hq).property) (hright := ofQComplex_valid _)
    (latticeProductError_segment_zero p q hp hq hdom he)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (pairedGlobalOffPoleAssemblyMap.eval q (compose_inner_mem hq).1).property
      (shiftedLatticeKernelMap.eval q (compose_inner_mem hq).2).property)
    (hright := pairedRiccatiCenterConstant.property)
  let P := gridScalarValue (pairedGlobalOffPoleAssemblyMap.eval q (compose_inner_mem hq).1)
  let Q := gridScalarValue (shiftedLatticeKernelMap.eval q (compose_inner_mem hq).2)
  let C := gridScalarValue pairedRiccatiCenterConstant
  change -C+1*(P*Q)=0 at hz
  change P*Q=C
  grind only

end
end ComputableAnalysis.ModularForms
