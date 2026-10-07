import ComputableAnalysis.ModularForms.LatticeHalfShiftLocalUniqueness

/-! Exact product identity for the actual lattice kernel near its pole. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option maxHeartbeats 1000000

theorem latticeHalfShiftLocal_original_mem (z : Scalar) (hz : latticeHalfShiftLocalDomain z)
    (hn : NonzeroBoxSearch.Nonzero z) : pairedOffPoleDomain z :=
  pairedZeroLaurentMap_global_mem z
    ⟨pairedPoleExtension_room z (compose_inner_mem (latticeHalfShiftLocal_mem z hz).2),hn⟩

theorem latticeHalfShiftLocal_original_mul_reciprocal (z : Scalar)
    (hz : latticeHalfShiftLocalDomain z) (hn : NonzeroBoxSearch.Nonzero z) :
    (mul (pairedGlobalOffPoleAssemblyMap.eval z (latticeHalfShiftLocal_original_mem z hz hn)).val
      (pairedRegularizedLaurentReciprocalMap.eval z
        (compose_inner_mem (latticeHalfShiftLocal_mem z hz).2)).val).Equiv (ofQComplex QComplex.one) := by
  let hw := compose_inner_mem (latticeHalfShiftLocal_mem z hz).2
  let hl : pairedZeroLaurentMap.domain z := ⟨pairedPoleExtension_room z hw,hn⟩
  let hs := LocalODE.interior_bound _ z hw
  let p := pairedZeroLaurentMap.eval z hl
  let w := pairedPoleReciprocal z hl.1 hs
  let g := pairedGlobalOffPoleAssemblyMap.eval z (latticeHalfShiftLocal_original_mem z hz hn)
  let v := pairedRegularizedLaurentReciprocalMap.eval z hw
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid p.property w.property) (hright := ofQComplex_valid _)
    (pairedZeroLaurent_mul_poleReciprocal z hl hs)
  have hg := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := p.property) (hright := g.property)
    (pairedZeroLaurentMap_global_agreement z hl)
  have hv := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := v.property) (hright := w.property)
    (pairedRegularizedLaurentReciprocal_value z hw)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := mul_valid g.property v.property)
    (hright := ofQComplex_valid _)
  let P := gridScalarValue p
  let W := gridScalarValue w
  let G := gridScalarValue g
  let V := gridScalarValue v
  change P*W=1 at hp
  change P=G at hg
  change V=W at hv
  change G*V=1
  rw [←hg,hv]
  exact hp

theorem latticeHalfShiftLocal_product_identity (z : Scalar)
    (hz : latticeHalfShiftLocalDomain z) (hn : NonzeroBoxSearch.Nonzero z) :
    (mul (pairedGlobalOffPoleAssemblyMap.eval z (latticeHalfShiftLocal_original_mem z hz hn)).val
      (shiftedLatticeKernelMap.eval z (latticeHalfShiftLocal_mem z hz).1).val).Equiv
      pairedRiccatiCenterConstant.val := by
  let hm := latticeHalfShiftLocal_mem z hz
  let p := pairedGlobalOffPoleAssemblyMap.eval z (latticeHalfShiftLocal_original_mem z hz hn)
  let q := shiftedLatticeKernelMap.eval z hm.1
  let w := pairedRegularizedLaurentReciprocalMap.eval z (compose_inner_mem hm.2)
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid p.property w.property)
    (hright := ofQComplex_valid _) (latticeHalfShiftLocal_original_mul_reciprocal z hz hn)
  have hq := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := q.property)
    (hright := (scaledLatticeReciprocalMap.eval z hm.2).property) (latticeHalfShiftLocal_agreement z hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := mul_valid p.property q.property)
    (hright := pairedRiccatiCenterConstant.property)
  let P := gridScalarValue p
  let Q := gridScalarValue q
  let W := gridScalarValue w
  let C := gridScalarValue pairedRiccatiCenterConstant
  change P*W=1 at hp
  change Q=0+C*W at hq
  change P*Q=C
  rw [hq]
  grind only

def latticeHalfShiftLocalInverse (z : Scalar) (hz : latticeHalfShiftLocalDomain z)
    (hn : NonzeroBoxSearch.Nonzero z) : Scalar :=
  DomainFunctions.scalarProduct
    (pairedGlobalOffPoleAssemblyMap.eval z (latticeHalfShiftLocal_original_mem z hz hn))
    pairedRiccatiCenterInverse

theorem latticeHalfShiftLocal_inverse_identity (z : Scalar) (hz : latticeHalfShiftLocalDomain z)
    (hn : NonzeroBoxSearch.Nonzero z) :
    (mul (shiftedLatticeKernelMap.eval z (latticeHalfShiftLocal_mem z hz).1).val
      (latticeHalfShiftLocalInverse z hz hn).val).Equiv (ofQComplex QComplex.one) := by
  let p := pairedGlobalOffPoleAssemblyMap.eval z (latticeHalfShiftLocal_original_mem z hz hn)
  let q := shiftedLatticeKernelMap.eval z (latticeHalfShiftLocal_mem z hz).1
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid p.property q.property)
    (hright := pairedRiccatiCenterConstant.property) (latticeHalfShiftLocal_product_identity z hz hn)
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid pairedRiccatiCenterConstant.property pairedRiccatiCenterInverse.property)
    (hright := ofQComplex_valid _) pairedRiccatiCenterConstant_mul_inverse
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid q.property (latticeHalfShiftLocalInverse z hz hn).property) (hright := ofQComplex_valid _)
  let P := gridScalarValue p
  let Q := gridScalarValue q
  let C := gridScalarValue pairedRiccatiCenterConstant
  let I := gridScalarValue pairedRiccatiCenterInverse
  change P*Q=C at hp
  change C*I=1 at hi
  change Q*(P*I)=1
  grind only

theorem latticeHalfShiftLocal_shifted_nonzero (z : Scalar) (hz : latticeHalfShiftLocalDomain z)
    (hn : NonzeroBoxSearch.Nonzero z) :
    NonzeroBoxSearch.Nonzero (shiftedLatticeKernelMap.eval z (latticeHalfShiftLocal_mem z hz).1) :=
  RepresentedReciprocal.nonzero_of_inverse _ (latticeHalfShiftLocalInverse z hz hn)
    (latticeHalfShiftLocal_inverse_identity z hz hn)

end ComputableAnalysis.ModularForms
