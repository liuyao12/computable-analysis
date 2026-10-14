import ComputableAnalysis.ModularForms.ContinuedLatticeReciprocal
import ComputableAnalysis.ModularForms.PairedGlobalOffPoleIntegerPeriodicity

/-! Agreement with the local regularization and exact upper-half-plane periods. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
noncomputable section

theorem continuedLatticeReciprocal_local_mem (z : Scalar) (hz : latticeHalfShiftLocalDomain z) :
    continuedLatticeReciprocalMap.domain z := ⟨(latticeHalfShiftLocal_mem z hz).1,trivial⟩

theorem continuedLatticeReciprocal_local_agreement (z : Scalar) (hz : latticeHalfShiftLocalDomain z) :
    (continuedLatticeReciprocalMap.eval z (continuedLatticeReciprocal_local_mem z hz)).val.Equiv
      (pairedRegularizedLaurentReciprocalMap.eval z
        (compose_inner_mem (latticeHalfShiftLocal_mem z hz).2)).val := by
  let hm := latticeHalfShiftLocal_mem z hz
  let q := shiftedLatticeKernelMap.eval z hm.1
  let w := pairedRegularizedLaurentReciprocalMap.eval z (compose_inner_mem hm.2)
  have hq := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := q.property)
    (hright := (scaledLatticeReciprocalMap.eval z hm.2).property)
    (latticeHalfShiftLocal_agreement z hz)
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid pairedRiccatiCenterConstant.property pairedRiccatiCenterInverse.property)
    (hright := ofQComplex_valid _) pairedRiccatiCenterConstant_mul_inverse
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (continuedLatticeReciprocalMap.eval z (continuedLatticeReciprocal_local_mem z hz)).property)
    (hright := w.property)
  let Q := gridScalarValue q
  let W := gridScalarValue w
  let C := gridScalarValue pairedRiccatiCenterConstant
  let I := gridScalarValue pairedRiccatiCenterInverse
  change Q=0+C*W at hq
  change C*I=1 at hi
  change 0+I*Q=W
  rw [hq]
  grind only

theorem continuedLatticeReciprocal_upper_period_int (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k : Int) :
    (continuedLatticeReciprocalMap.eval (integerShiftScalar z k)
      (continuedLatticeReciprocal_upper_mem _ (integerShiftScalar_upper z hz k))).val.Equiv
      (continuedLatticeReciprocalMap.eval z (continuedLatticeReciprocal_upper_mem z hz)).val := by
  let w := integerShiftScalar z k
  let hw := integerShiftScalar_upper z hz k
  let p := pairedGlobalOffPoleAssemblyMap.eval z (pairedGlobalOffPole_upper_mem z hz)
  let q := pairedGlobalOffPoleAssemblyMap.eval w (pairedGlobalOffPole_upper_mem w hw)
  have hp : q.val.Equiv p.val :=
    globalOffPoleValue_period_int z (pairedGlobalOffPole_upper_mem z hz) k
  have hi := RepresentedReciprocal.inverse_congr q p
    (upperLatticeKernel_nonzero w hw) (upperLatticeKernel_nonzero z hz) hp
  have hq := continuedLatticeReciprocal_represented_inverse w hw
  have hz' := continuedLatticeReciprocal_represented_inverse z hz
  exact equiv_trans
    (continuedLatticeReciprocalMap.eval w (continuedLatticeReciprocal_upper_mem w hw)).property
    (RepresentedReciprocal.inverse q (upperLatticeKernel_nonzero w hw)).property
    (continuedLatticeReciprocalMap.eval z (continuedLatticeReciprocal_upper_mem z hz)).property
    (equiv_symm hq)
    (equiv_trans (RepresentedReciprocal.inverse q (upperLatticeKernel_nonzero w hw)).property
      (RepresentedReciprocal.inverse p (upperLatticeKernel_nonzero z hz)).property
      (continuedLatticeReciprocalMap.eval z (continuedLatticeReciprocal_upper_mem z hz)).property hi hz')

end
end ComputableAnalysis.ModularForms
