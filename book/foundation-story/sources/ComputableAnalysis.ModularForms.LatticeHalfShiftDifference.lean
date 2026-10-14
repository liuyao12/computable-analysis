import ComputableAnalysis.ModularForms.LatticeHalfShiftEquation
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicIntersectionSum

/-! A proved comparison equation for the actual regularized lattice and nome maps.
Both actual constructions use the proved lattice Riccati constant. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option maxHeartbeats 1000000

def latticeHalfShiftDifferenceMap : DomainFunctions.Map :=
  intersectionSum shiftedLatticeKernelMap
    (negate scaledLatticeReciprocalMap)

noncomputable def latticeHalfShiftDifferenceMap_holomorphic :
    Holomorphic latticeHalfShiftDifferenceMap :=
  shiftedLatticeKernelMap_holomorphic.intersectionSum
    scaledLatticeReciprocalMap_holomorphic.negate

theorem latticeHalfShiftDifference_differential_identity (z : Scalar)
    (hz : latticeHalfShiftDifferenceMap.domain z) :
    (latticeHalfShiftDifferenceMap_holomorphic.derivative z hz).val.Equiv
      (neg (mul (add (shiftedLatticeKernelMap.eval z hz.1).val
        (scaledLatticeReciprocalMap.eval z hz.2).val)
        (latticeHalfShiftDifferenceMap.eval z hz).val)) := by
  let q := shiftedLatticeKernelMap.eval z hz.1
  let s := scaledLatticeReciprocalMap.eval z hz.2
  let dq := shiftedLatticeKernelMap_holomorphic.derivative z hz.1
  let ds := scaledLatticeReciprocalMap_holomorphic.derivative z hz.2
  have hq := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := dq.property)
    (hright := sub_valid pairedRiccatiCenterConstant.property (mul_valid q.property q.property))
    (shiftedLatticeKernel_differential_identity z hz.1)
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := ds.property)
    (hright := sub_valid pairedRiccatiCenterConstant.property (mul_valid s.property s.property))
    (scaledLatticeReciprocal_differential_identity z hz.2)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeHalfShiftDifferenceMap_holomorphic.derivative z hz).property)
    (hright := neg_valid (mul_valid (add_valid q.property s.property)
      (latticeHalfShiftDifferenceMap.eval z hz).property))
  let Q := gridScalarValue q
  let S := gridScalarValue s
  let DQ := gridScalarValue dq
  let DS := gridScalarValue ds
  let C := gridScalarValue pairedRiccatiCenterConstant
  change DQ=C-Q*Q at hq
  change DS=C-S*S at hs
  change DQ+ -DS= -((Q+S)*(Q+ -S))
  rw [hq,hs]
  grind only

theorem latticeHalfShiftDifference_center (z : Scalar)
    (hz : latticeHalfShiftDifferenceMap.domain z) (he : z.val.Equiv zero) :
    (latticeHalfShiftDifferenceMap.eval z hz).val.Equiv zero := by
  have hw := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (shiftedLatticeKernelMap.eval z hz.1).property)
    (hright := ofQComplex_valid _) (shiftedLatticeKernel_center_zero z he)
  have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (scaledLatticeReciprocalMap.eval z hz.2).property)
    (hright := ofQComplex_valid _) (scaledLatticeReciprocal_center_zero z hz.2 he)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeHalfShiftDifferenceMap.eval z hz).property)
    (hright := ofQComplex_valid _)
  change _=(0:ScalarAlgebra.Value)
  change gridScalarValue (shiftedLatticeKernelMap.eval z hz.1)=0 at hw
  change gridScalarValue (scaledLatticeReciprocalMap.eval z hz.2)=0 at hv
  change gridScalarValue (shiftedLatticeKernelMap.eval z hz.1)+
    -gridScalarValue (scaledLatticeReciprocalMap.eval z hz.2)=0
  rw [hw,hv]
  grind only

theorem latticeHalfShiftDifference_derivative_center (z : Scalar)
    (hz : latticeHalfShiftDifferenceMap.domain z) (he : z.val.Equiv zero) :
    (latticeHalfShiftDifferenceMap_holomorphic.derivative z hz).val.Equiv zero := by
  have hw := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (shiftedLatticeKernelMap_holomorphic.derivative z hz.1).property)
    (hright := pairedRiccatiCenterConstant.property) (shiftedLatticeKernel_center_derivative z he)
  have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (scaledLatticeReciprocalMap_holomorphic.derivative z hz.2).property)
    (hright := pairedRiccatiCenterConstant.property) (scaledLatticeReciprocal_center_derivative z hz.2 he)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeHalfShiftDifferenceMap_holomorphic.derivative z hz).property)
    (hright := ofQComplex_valid _)
  change _=(0:ScalarAlgebra.Value)
  change gridScalarValue (shiftedLatticeKernelMap_holomorphic.derivative z hz.1)=gridScalarValue pairedRiccatiCenterConstant at hw
  change gridScalarValue (scaledLatticeReciprocalMap_holomorphic.derivative z hz.2)=gridScalarValue pairedRiccatiCenterConstant at hv
  change gridScalarValue (shiftedLatticeKernelMap_holomorphic.derivative z hz.1)+
    -gridScalarValue (scaledLatticeReciprocalMap_holomorphic.derivative z hz.2)=0
  rw [hw,hv]
  grind only

theorem latticeHalfShiftDifference_zero_mem : latticeHalfShiftDifferenceMap.domain pairedZeroScalar := by
  refine ⟨shiftedLatticeKernel_center_mem _ (equiv_refl _ (ofQComplex_valid _)),?_,⟩
  refine ⟨?_,trivial⟩
  exact ⟨0,by decide +kernel,by decide +kernel,Small.zero (by decide +kernel)⟩

noncomputable def latticeHalfShiftDifference_centerDerivative :
    HasDerivativeAt latticeHalfShiftDifferenceMap pairedZeroScalar latticeHalfShiftDifference_zero_mem
      ⟨zero,ofQComplex_valid _⟩ :=
  (latticeHalfShiftDifferenceMap_holomorphic.atPoint pairedZeroScalar latticeHalfShiftDifference_zero_mem).congrDerivative (latticeHalfShiftDifference_derivative_center pairedZeroScalar
      latticeHalfShiftDifference_zero_mem (equiv_refl _ (ofQComplex_valid _)))

theorem latticeHalfShiftDifference_center_error (eps H : QPos) (z : Scalar)
    (hz : latticeHalfShiftDifferenceMap.domain z)
    (hH : H.val≤(latticeHalfShiftDifference_centerDerivative.delta eps).val)
    (hs : Small (sub z.val pairedZeroScalar.val) H.val) :
    Small (latticeHalfShiftDifferenceMap.eval z hz).val (eps.val*H.val) := by
  have hr := latticeHalfShiftDifference_centerDerivative.estimate eps H z hz hH hs
  have h0 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (latticeHalfShiftDifferenceMap.eval pairedZeroScalar latticeHalfShiftDifference_zero_mem).property)
    (hright := ofQComplex_valid _)
    (latticeHalfShiftDifference_center pairedZeroScalar latticeHalfShiftDifference_zero_mem
      (equiv_refl _ (ofQComplex_valid _)))
  have he : (DomainFunctions.remainder latticeHalfShiftDifferenceMap pairedZeroScalar latticeHalfShiftDifference_zero_mem
      ⟨zero,ofQComplex_valid _⟩ z hz).Equiv (latticeHalfShiftDifferenceMap.eval z hz).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := DomainFunctions.remainder_valid _ _ _ _ _ _) (hright := (latticeHalfShiftDifferenceMap.eval z hz).property)
    let F := gridScalarValue (latticeHalfShiftDifferenceMap.eval z hz)
    let A := gridScalarValue (latticeHalfShiftDifferenceMap.eval pairedZeroScalar latticeHalfShiftDifference_zero_mem)
    let Z := gridScalarValue z
    change A=0 at h0
    change (F-A)-0*(Z-0)=F
    rw [h0]
    grind only
  exact Small.congr (DomainFunctions.remainder_valid _ _ _ _ _ _)
    (latticeHalfShiftDifferenceMap.eval z hz).property he hr

end ComputableAnalysis.ModularForms
