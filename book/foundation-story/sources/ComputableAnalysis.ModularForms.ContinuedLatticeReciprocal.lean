import ComputableAnalysis.ModularForms.UpperLatticeKernelInverse

/-! Holomorphic continuation of the lattice reciprocal through its zero at the origin. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
noncomputable section

def continuedLatticeReciprocalMap : DomainFunctions.Map :=
  compose (affine ⟨zero,ofQComplex_valid _⟩ pairedRiccatiCenterInverse) shiftedLatticeKernelMap

def continuedLatticeReciprocalMap_holomorphic : Holomorphic continuedLatticeReciprocalMap :=
  (affine_holomorphic ⟨zero,ofQComplex_valid _⟩ pairedRiccatiCenterInverse).compose
    shiftedLatticeKernelMap_holomorphic

theorem continuedLatticeReciprocal_differential_identity (z : Scalar)
    (hz : continuedLatticeReciprocalMap.domain z) :
    (continuedLatticeReciprocalMap_holomorphic.derivative z hz).val.Equiv
      (sub (ofQComplex QComplex.one)
        (mul pairedRiccatiCenterConstant.val
          (mul (continuedLatticeReciprocalMap.eval z hz).val
            (continuedLatticeReciprocalMap.eval z hz).val))) := by
  let hq := compose_inner_mem hz
  let q := shiftedLatticeKernelMap.eval z hq
  let d := shiftedLatticeKernelMap_holomorphic.derivative z hq
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := d.property)
    (hright := sub_valid pairedRiccatiCenterConstant.property (mul_valid q.property q.property))
    (shiftedLatticeKernel_differential_identity z hq)
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid pairedRiccatiCenterConstant.property pairedRiccatiCenterInverse.property)
    (hright := ofQComplex_valid _) pairedRiccatiCenterConstant_mul_inverse
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (continuedLatticeReciprocalMap_holomorphic.derivative z hz).property)
    (hright := sub_valid (ofQComplex_valid _) (mul_valid pairedRiccatiCenterConstant.property
      (mul_valid (continuedLatticeReciprocalMap.eval z hz).property
        (continuedLatticeReciprocalMap.eval z hz).property)))
  let Q := gridScalarValue q
  let D := gridScalarValue d
  let C := gridScalarValue pairedRiccatiCenterConstant
  let I := gridScalarValue pairedRiccatiCenterInverse
  change D=C-Q*Q at hd
  change C*I=1 at hi
  change I*D=1-C*((0+I*Q)*(0+I*Q))
  rw [hd]
  grind only

theorem continuedLatticeReciprocal_center_mem (z : Scalar) (he : z.val.Equiv zero) :
    continuedLatticeReciprocalMap.domain z := ⟨shiftedLatticeKernel_center_mem z he,trivial⟩

theorem continuedLatticeReciprocal_center_zero (z : Scalar) (he : z.val.Equiv zero) :
    (continuedLatticeReciprocalMap.eval z (continuedLatticeReciprocal_center_mem z he)).val.Equiv zero := by
  have hq := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (shiftedLatticeKernelMap.eval z (shiftedLatticeKernel_center_mem z he)).property)
    (hright := ofQComplex_valid _) (shiftedLatticeKernel_center_zero z he)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (continuedLatticeReciprocalMap.eval z (continuedLatticeReciprocal_center_mem z he)).property)
    (hright := ofQComplex_valid _)
  let Q := gridScalarValue (shiftedLatticeKernelMap.eval z (shiftedLatticeKernel_center_mem z he))
  let I := gridScalarValue pairedRiccatiCenterInverse
  change Q=0 at hq
  change 0+I*Q=0
  rw [hq]
  grind only

theorem continuedLatticeReciprocal_upper_mem (z : Scalar) (hz : InUpperHalfPlane z.val) :
    continuedLatticeReciprocalMap.domain z :=
  ⟨(compose_inner_mem (latticeProductError_upper_mem z hz)).2,trivial⟩

theorem continuedLatticeReciprocal_upper_agreement (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (continuedLatticeReciprocalMap.eval z (continuedLatticeReciprocal_upper_mem z hz)).val.Equiv
      (upperLatticeKernelInverse z hz).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (continuedLatticeReciprocalMap.eval z (continuedLatticeReciprocal_upper_mem z hz)).property)
    (hright := (upperLatticeKernelInverse z hz).property)
  let Q := gridScalarValue (shiftedLatticeKernelMap.eval z
    (compose_inner_mem (latticeProductError_upper_mem z hz)).2)
  let I := gridScalarValue pairedRiccatiCenterInverse
  change 0+I*Q=Q*I
  grind only

theorem continuedLatticeReciprocal_center_derivative (z : Scalar) (he : z.val.Equiv zero) :
    (continuedLatticeReciprocalMap_holomorphic.derivative z
      (continuedLatticeReciprocal_center_mem z he)).val.Equiv (ofQComplex QComplex.one) := by
  let hz := continuedLatticeReciprocal_center_mem z he
  let w := continuedLatticeReciprocalMap.eval z hz
  let d := continuedLatticeReciprocalMap_holomorphic.derivative z hz
  have hw := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := w.property)
    (hright := ofQComplex_valid _) (continuedLatticeReciprocal_center_zero z he)
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := d.property)
    (hright := sub_valid (ofQComplex_valid _)
      (mul_valid pairedRiccatiCenterConstant.property (mul_valid w.property w.property)))
    (continuedLatticeReciprocal_differential_identity z hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := d.property) (hright := ofQComplex_valid _)
  let W := gridScalarValue w
  let D := gridScalarValue d
  let C := gridScalarValue pairedRiccatiCenterConstant
  change W=0 at hw
  change D=1-C*(W*W) at hd
  change D=1
  rw [hw] at hd
  grind only

theorem continuedLatticeReciprocal_represented_inverse (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (RepresentedReciprocal.inverse
      (pairedGlobalOffPoleAssemblyMap.eval z (pairedGlobalOffPole_upper_mem z hz))
      (upperLatticeKernel_nonzero z hz)).val.Equiv
      (continuedLatticeReciprocalMap.eval z (continuedLatticeReciprocal_upper_mem z hz)).val := by
  have hi := RepresentedReciprocal.inverse_unique
    (pairedGlobalOffPoleAssemblyMap.eval z (pairedGlobalOffPole_upper_mem z hz))
    (upperLatticeKernel_nonzero z hz) (upperLatticeKernelInverse z hz)
    (upperLatticeKernel_mul_inverse z hz)
  exact equiv_trans
    (RepresentedReciprocal.inverse
      (pairedGlobalOffPoleAssemblyMap.eval z (pairedGlobalOffPole_upper_mem z hz))
      (upperLatticeKernel_nonzero z hz)).property
    (upperLatticeKernelInverse z hz).property
    (continuedLatticeReciprocalMap.eval z (continuedLatticeReciprocal_upper_mem z hz)).property
    hi (equiv_symm (continuedLatticeReciprocal_upper_agreement z hz))

end
end ComputableAnalysis.ModularForms
