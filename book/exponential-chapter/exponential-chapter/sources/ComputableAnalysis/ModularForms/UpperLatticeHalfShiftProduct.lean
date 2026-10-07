import ComputableAnalysis.ModularForms.UpperHalfPlaneSegments

/-! The actual lattice half-shift product identity throughout the upper half-plane. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
noncomputable section
set_option maxHeartbeats 2000000

def upperLatticeProductAnchor : Scalar :=
  ⟨ofQComplex ⟨0,latticeHalfShiftUniquenessRadius.val/2⟩,ofQComplex_valid _⟩

theorem upperLatticeProductAnchor_upper : InUpperHalfPlane upperLatticeProductAnchor.val := by
  refine ⟨0,?_⟩
  change 0<latticeHalfShiftUniquenessRadius.val/2
  rw [Rat.div_def]
  exact Rat.mul_pos latticeHalfShiftUniquenessRadius.property (by decide +kernel)

theorem upperLatticeProductAnchor_local : latticeHalfShiftLocalDomain upperLatticeProductAnchor := by
  let R := latticeHalfShiftUniquenessRadius.val
  have hp : 0<R := latticeHalfShiftUniquenessRadius.property
  have hs : Small upperLatticeProductAnchor.val R := by
    refine ⟨?_,?_,?_,?_⟩ <;> intro n m
    · change -R≤0; grind only
    · change 0≤R; exact Rat.le_of_lt hp
    · change -R≤R/2; grind only
    · change R/2≤R; grind only
  have he : upperLatticeProductAnchor.val.Equiv (sub upperLatticeProductAnchor.val pairedZeroScalar.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := upperLatticeProductAnchor.property) (hright := sub_valid upperLatticeProductAnchor.property pairedZeroScalar.property)
    let A := gridScalarValue upperLatticeProductAnchor
    change A=A-0
    grind only
  exact Small.congr upperLatticeProductAnchor.property
    (sub_valid upperLatticeProductAnchor.property pairedZeroScalar.property) he hs

theorem upperLatticeProductAnchor_error_zero :
    (latticeHalfShiftProductErrorMap.eval upperLatticeProductAnchor
      (latticeProductError_upper_mem upperLatticeProductAnchor upperLatticeProductAnchor_upper)).val.Equiv zero :=
  latticeHalfShiftProductError_local_zero upperLatticeProductAnchor upperLatticeProductAnchor_local
    (upperScalar_nonzero upperLatticeProductAnchor upperLatticeProductAnchor_upper)

theorem latticeProductError_upper_zero (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (latticeHalfShiftProductErrorMap.eval z (latticeProductError_upper_mem z hz)).val.Equiv zero :=
  latticeProductError_upper_segment_zero upperLatticeProductAnchor z upperLatticeProductAnchor_upper hz
    upperLatticeProductAnchor_error_zero

theorem latticeHalfShift_upper_product_identity (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (mul (pairedGlobalOffPoleAssemblyMap.eval z (pairedGlobalOffPole_upper_mem z hz)).val
      (shiftedLatticeKernelMap.eval z (compose_inner_mem (latticeProductError_upper_mem z hz)).2).val).Equiv
      pairedRiccatiCenterConstant.val :=
  latticeProductError_segment_product upperLatticeProductAnchor z
    (latticeProductError_upper_mem upperLatticeProductAnchor upperLatticeProductAnchor_upper)
    (latticeProductError_upper_mem z hz)
    (latticeProductError_upper_segment_mem upperLatticeProductAnchor z upperLatticeProductAnchor_upper hz)
    upperLatticeProductAnchor_error_zero

end
end ComputableAnalysis.ModularForms
