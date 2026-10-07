import ComputableAnalysis.ModularForms.LatticeHalfShiftDifference

/-! A constructed local domain and coefficient bound for the actual difference ODE. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option maxHeartbeats 1000000

def latticeHalfShiftCoefficientMap : DomainFunctions.Map :=
  negate (intersectionSum shiftedLatticeKernelMap scaledLatticeReciprocalMap)

noncomputable def latticeHalfShiftCoefficientMap_holomorphic : Holomorphic latticeHalfShiftCoefficientMap :=
  (shiftedLatticeKernelMap_holomorphic.intersectionSum scaledLatticeReciprocalMap_holomorphic).negate

theorem latticeHalfShiftCoefficient_center_zero :
    (latticeHalfShiftCoefficientMap.eval pairedZeroScalar latticeHalfShiftDifference_zero_mem).val.Equiv zero := by
  let hz := latticeHalfShiftDifference_zero_mem
  have hq := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (shiftedLatticeKernelMap.eval pairedZeroScalar hz.1).property) (hright := ofQComplex_valid _)
    (shiftedLatticeKernel_center_zero pairedZeroScalar (equiv_refl _ (ofQComplex_valid _)))
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (scaledLatticeReciprocalMap.eval pairedZeroScalar hz.2).property) (hright := ofQComplex_valid _)
    (scaledLatticeReciprocal_center_zero pairedZeroScalar hz.2 (equiv_refl _ (ofQComplex_valid _)))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeHalfShiftCoefficientMap.eval pairedZeroScalar hz).property) (hright := ofQComplex_valid _)
  let Q := gridScalarValue (shiftedLatticeKernelMap.eval pairedZeroScalar hz.1)
  let S := gridScalarValue (scaledLatticeReciprocalMap.eval pairedZeroScalar hz.2)
  change Q=0 at hq
  change S=0 at hs
  change -(Q+S)=(0:ScalarAlgebra.Value)
  rw [hq,hs]
  grind only

noncomputable def latticeHalfShiftCoefficient_centerContinuous :
    ContinuousAt latticeHalfShiftCoefficientMap pairedZeroScalar latticeHalfShiftDifference_zero_mem :=
  (latticeHalfShiftCoefficientMap_holomorphic.atPoint pairedZeroScalar latticeHalfShiftDifference_zero_mem).continuousAt

noncomputable def latticeHalfShiftComparisonRadius : QPos :=
  minRadius (latticeHalfShiftDifferenceMap_holomorphic.openDomain.radius pairedZeroScalar
    latticeHalfShiftDifference_zero_mem)
    (minRadius (latticeHalfShiftCoefficient_centerContinuous.delta unitError) ⟨1/4,by decide +kernel⟩)

theorem latticeHalfShiftComparisonRadius_short : latticeHalfShiftComparisonRadius.val≤(1:Rat)/4 :=
  Rat.le_trans (minRadius_right _ _) (minRadius_right _ _)

theorem latticeHalfShiftComparison_mem (z : Scalar)
    (hs : Small (sub z.val pairedZeroScalar.val) latticeHalfShiftComparisonRadius.val) :
    latticeHalfShiftDifferenceMap.domain z :=
  latticeHalfShiftDifferenceMap_holomorphic.openDomain.inside pairedZeroScalar
    latticeHalfShiftDifference_zero_mem z (hs.mono (minRadius_left _ _))

theorem latticeHalfShiftCoefficient_local_bound (z : Scalar)
    (hz : latticeHalfShiftDifferenceMap.domain z)
    (hs : Small (sub z.val pairedZeroScalar.val) latticeHalfShiftComparisonRadius.val) :
    Small (latticeHalfShiftCoefficientMap.eval z hz).val 1 := by
  have hr := latticeHalfShiftCoefficient_centerContinuous.estimate unitError z hz
    (hs.mono (Rat.le_trans (minRadius_right _ _) (minRadius_left _ _)))
  have he : (sub (latticeHalfShiftCoefficientMap.eval z hz).val
      (latticeHalfShiftCoefficientMap.eval pairedZeroScalar latticeHalfShiftDifference_zero_mem).val).Equiv
      (latticeHalfShiftCoefficientMap.eval z hz).val := by
    have h0 := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (latticeHalfShiftCoefficientMap.eval pairedZeroScalar latticeHalfShiftDifference_zero_mem).property)
      (hright := ofQComplex_valid _) latticeHalfShiftCoefficient_center_zero
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (latticeHalfShiftCoefficientMap.eval z hz).property
        (latticeHalfShiftCoefficientMap.eval pairedZeroScalar latticeHalfShiftDifference_zero_mem).property)
      (hright := (latticeHalfShiftCoefficientMap.eval z hz).property)
    let C := gridScalarValue (latticeHalfShiftCoefficientMap.eval z hz)
    let Z := gridScalarValue (latticeHalfShiftCoefficientMap.eval pairedZeroScalar latticeHalfShiftDifference_zero_mem)
    change Z=0 at h0
    change C-Z=C
    rw [h0]
    grind only
  exact Small.congr (sub_valid (latticeHalfShiftCoefficientMap.eval z hz).property
    (latticeHalfShiftCoefficientMap.eval pairedZeroScalar latticeHalfShiftDifference_zero_mem).property)
    (latticeHalfShiftCoefficientMap.eval z hz).property he hr

theorem latticeHalfShiftDifference_coefficient_equation (z : Scalar)
    (hz : latticeHalfShiftDifferenceMap.domain z) :
    (latticeHalfShiftDifferenceMap_holomorphic.derivative z hz).val.Equiv
      (mul (latticeHalfShiftCoefficientMap.eval z hz).val
        (latticeHalfShiftDifferenceMap.eval z hz).val) := by
  let q := shiftedLatticeKernelMap.eval z hz.1
  let v := scaledLatticeReciprocalMap.eval z hz.2
  let h := latticeHalfShiftDifferenceMap.eval z hz
  let d := latticeHalfShiftDifferenceMap_holomorphic.derivative z hz
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := d.property)
    (hright := neg_valid (mul_valid (add_valid q.property v.property) h.property))
    (latticeHalfShiftDifference_differential_identity z hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := d.property)
    (hright := mul_valid (latticeHalfShiftCoefficientMap.eval z hz).property h.property)
  let Q := gridScalarValue q
  let V := gridScalarValue v
  let H := gridScalarValue h
  let D := gridScalarValue d
  change D= -((Q+V)*H) at hd
  change D= -(Q+V)*H
  rw [hd]
  grind only

end ComputableAnalysis.ModularForms
