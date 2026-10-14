import ComputableAnalysis.ModularForms.UpperLatticeHalfShiftProduct

/-! An explicit inverse of the lattice kernel throughout the upper half-plane. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
noncomputable section

def upperLatticeKernelInverse (z : Scalar) (hz : InUpperHalfPlane z.val) : Scalar :=
  scalarProduct
    (shiftedLatticeKernelMap.eval z (compose_inner_mem (latticeProductError_upper_mem z hz)).2)
    pairedRiccatiCenterInverse

theorem upperLatticeKernel_mul_inverse (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (mul (pairedGlobalOffPoleAssemblyMap.eval z (pairedGlobalOffPole_upper_mem z hz)).val
      (upperLatticeKernelInverse z hz).val).Equiv (ofQComplex QComplex.one) := by
  let p := pairedGlobalOffPoleAssemblyMap.eval z (pairedGlobalOffPole_upper_mem z hz)
  let q := shiftedLatticeKernelMap.eval z (compose_inner_mem (latticeProductError_upper_mem z hz)).2
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid p.property q.property)
    (hright := pairedRiccatiCenterConstant.property) (latticeHalfShift_upper_product_identity z hz)
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid pairedRiccatiCenterConstant.property pairedRiccatiCenterInverse.property)
    (hright := ofQComplex_valid _) pairedRiccatiCenterConstant_mul_inverse
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid p.property (upperLatticeKernelInverse z hz).property)
    (hright := ofQComplex_valid _)
  let P := gridScalarValue p
  let Q := gridScalarValue q
  let C := gridScalarValue pairedRiccatiCenterConstant
  let I := gridScalarValue pairedRiccatiCenterInverse
  change P*Q=C at hp
  change C*I=1 at hi
  change P*(Q*I)=1
  grind only

theorem upperLatticeKernel_nonzero (z : Scalar) (hz : InUpperHalfPlane z.val) :
    NonzeroBoxSearch.Nonzero
      (pairedGlobalOffPoleAssemblyMap.eval z (pairedGlobalOffPole_upper_mem z hz)) :=
  RepresentedReciprocal.nonzero_of_inverse _ (upperLatticeKernelInverse z hz)
    (upperLatticeKernel_mul_inverse z hz)

end
end ComputableAnalysis.ModularForms
