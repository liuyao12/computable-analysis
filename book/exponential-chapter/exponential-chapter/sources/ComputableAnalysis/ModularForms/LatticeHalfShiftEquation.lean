import ComputableAnalysis.ModularForms.PairedLaurentReciprocalEquation
import ComputableAnalysis.ModularForms.LatticeHalfPeriodSimpleZero

/-! The actual lattice kernel shifted to its regular half-period. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def latticeHalfShiftMap : DomainFunctions.Map :=
  affine latticeHalfPoint ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩

def latticeHalfShiftMap_holomorphic : Holomorphic latticeHalfShiftMap :=
  affine_holomorphic latticeHalfPoint ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩

def shiftedLatticeKernelMap : DomainFunctions.Map :=
  compose pairedGlobalOffPoleAssemblyMap latticeHalfShiftMap

noncomputable def shiftedLatticeKernelMap_holomorphic : Holomorphic shiftedLatticeKernelMap :=
  pairedGlobalOffPoleAssemblyMap_holomorphic.compose latticeHalfShiftMap_holomorphic

theorem latticeHalfShift_center (z : Scalar) (he : z.val.Equiv zero) :
    (latticeHalfShiftMap.eval z trivial).val.Equiv latticeHalfPoint.val := by
  have hz := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := z.property) (hright := ofQComplex_valid _) he
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeHalfShiftMap.eval z trivial).property) (hright := latticeHalfPoint.property)
  let Z := gridScalarValue z
  let H := gridScalarValue latticeHalfPoint
  change Z=0 at hz
  change H+1*Z=H
  rw [hz]
  grind only

theorem shiftedLatticeKernel_center_mem (z : Scalar) (he : z.val.Equiv zero) :
    shiftedLatticeKernelMap.domain z :=
  ⟨trivial,latticeHalfPeriod_mem _ (latticeHalfShift_center z he)⟩

theorem shiftedLatticeKernel_center_zero (z : Scalar) (he : z.val.Equiv zero) :
    (shiftedLatticeKernelMap.eval z (shiftedLatticeKernel_center_mem z he)).val.Equiv zero :=
  latticeHalfPeriod_value_zero _ (latticeHalfShift_center z he)

theorem shiftedLatticeKernel_differential_identity (z : Scalar)
    (hz : shiftedLatticeKernelMap.domain z) :
    (shiftedLatticeKernelMap_holomorphic.derivative z hz).val.Equiv
      (sub pairedRiccatiCenterConstant.val
        (mul (shiftedLatticeKernelMap.eval z hz).val (shiftedLatticeKernelMap.eval z hz).val)) := by
  let w := latticeHalfShiftMap.eval z (compose_inner_mem hz)
  let hw := compose_outer_mem hz
  let p := pairedGlobalOffPoleAssemblyMap.eval w hw
  let d := pairedGlobalOffPoleAssemblyMap_holomorphic.derivative w hw
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := add_valid d.property (mul_valid p.property p.property))
    (hright := pairedRiccatiCenterConstant.property)
    (pairedGlobalOffPoleAssemblyMap_riccati_identity w hw)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (shiftedLatticeKernelMap_holomorphic.derivative z hz).property)
    (hright := sub_valid pairedRiccatiCenterConstant.property
      (mul_valid (shiftedLatticeKernelMap.eval z hz).property (shiftedLatticeKernelMap.eval z hz).property))
  let P := gridScalarValue p
  let D := gridScalarValue d
  let C := gridScalarValue pairedRiccatiCenterConstant
  change D+P*P=C at hd
  change D*1=C-P*P
  grind only

theorem shiftedLatticeKernel_center_derivative (z : Scalar) (he : z.val.Equiv zero) :
    (shiftedLatticeKernelMap_holomorphic.derivative z (shiftedLatticeKernel_center_mem z he)).val.Equiv
      pairedRiccatiCenterConstant.val := by
  let hz := shiftedLatticeKernel_center_mem z he
  let p := shiftedLatticeKernelMap.eval z hz
  let d := shiftedLatticeKernelMap_holomorphic.derivative z hz
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := p.property) (hright := ofQComplex_valid _)
    (shiftedLatticeKernel_center_zero z he)
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := d.property)
    (hright := sub_valid pairedRiccatiCenterConstant.property (mul_valid p.property p.property))
    (shiftedLatticeKernel_differential_identity z hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := d.property) (hright := pairedRiccatiCenterConstant.property)
  let P := gridScalarValue p
  let D := gridScalarValue d
  let C := gridScalarValue pairedRiccatiCenterConstant
  change P=0 at hp
  change D=C-P*P at hd
  change D=C
  rw [hp] at hd
  grind only

def scaledLatticeReciprocalMap : DomainFunctions.Map :=
  compose (affine ⟨zero,ofQComplex_valid _⟩ pairedRiccatiCenterConstant)
    pairedRegularizedLaurentReciprocalMap

def scaledLatticeReciprocalMap_holomorphic : Holomorphic scaledLatticeReciprocalMap :=
  (affine_holomorphic ⟨zero,ofQComplex_valid _⟩ pairedRiccatiCenterConstant).compose
    pairedRegularizedLaurentReciprocalMap_holomorphic

theorem scaledLatticeReciprocal_differential_identity (z : Scalar)
    (hz : scaledLatticeReciprocalMap.domain z) :
    (scaledLatticeReciprocalMap_holomorphic.derivative z hz).val.Equiv
      (sub pairedRiccatiCenterConstant.val
        (mul (scaledLatticeReciprocalMap.eval z hz).val (scaledLatticeReciprocalMap.eval z hz).val)) := by
  let hw := compose_inner_mem hz
  let w := pairedRegularizedLaurentReciprocalMap.eval z hw
  let d := pairedRegularizedLaurentReciprocalMap_holomorphic.derivative z hw
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := d.property)
    (hright := sub_valid (ofQComplex_valid _)
      (mul_valid pairedRiccatiCenterConstant.property (mul_valid w.property w.property)))
    (pairedRegularizedLaurentReciprocal_differential_identity z hw)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scaledLatticeReciprocalMap_holomorphic.derivative z hz).property)
    (hright := sub_valid pairedRiccatiCenterConstant.property
      (mul_valid (scaledLatticeReciprocalMap.eval z hz).property (scaledLatticeReciprocalMap.eval z hz).property))
  let W := gridScalarValue w
  let D := gridScalarValue d
  let C := gridScalarValue pairedRiccatiCenterConstant
  change D=1-C*(W*W) at hd
  change C*D=C-(0+C*W)*(0+C*W)
  rw [hd]
  grind only

theorem scaledLatticeReciprocal_center_zero (z : Scalar)
    (hz : scaledLatticeReciprocalMap.domain z) (he : z.val.Equiv zero) :
    (scaledLatticeReciprocalMap.eval z hz).val.Equiv zero := by
  have hw := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedRegularizedLaurentReciprocalMap.eval z (compose_inner_mem hz)).property)
    (hright := ofQComplex_valid _) (pairedRegularizedLaurentReciprocal_center z (compose_inner_mem hz) he)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scaledLatticeReciprocalMap.eval z hz).property) (hright := ofQComplex_valid _)
  let W := gridScalarValue (pairedRegularizedLaurentReciprocalMap.eval z (compose_inner_mem hz))
  let C := gridScalarValue pairedRiccatiCenterConstant
  change W=0 at hw
  change 0+C*W=(0:ScalarAlgebra.Value)
  rw [hw]
  grind only

theorem scaledLatticeReciprocal_center_derivative (z : Scalar)
    (hz : scaledLatticeReciprocalMap.domain z) (he : z.val.Equiv zero) :
    (scaledLatticeReciprocalMap_holomorphic.derivative z hz).val.Equiv pairedRiccatiCenterConstant.val := by
  have hw := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedRegularizedLaurentReciprocalMap_holomorphic.derivative z (compose_inner_mem hz)).property)
    (hright := ofQComplex_valid _) (pairedRegularizedLaurentReciprocal_derivative_center z (compose_inner_mem hz) he)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scaledLatticeReciprocalMap_holomorphic.derivative z hz).property)
    (hright := pairedRiccatiCenterConstant.property)
  let D := gridScalarValue (pairedRegularizedLaurentReciprocalMap_holomorphic.derivative z (compose_inner_mem hz))
  let C := gridScalarValue pairedRiccatiCenterConstant
  change D=1 at hw
  change C*D=C
  rw [hw]
  grind only

end ComputableAnalysis.ModularForms
