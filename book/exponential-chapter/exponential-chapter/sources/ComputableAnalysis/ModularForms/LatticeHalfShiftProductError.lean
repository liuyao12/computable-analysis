import ComputableAnalysis.ModularForms.LatticeHalfShiftLocalProduct

/-! The actual global half-shift product error satisfies a homogeneous equation. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
noncomputable section
set_option maxHeartbeats 1000000

def latticeHalfShiftProductOpenData : ScalarTopology.OpenData
    (intersectionSum pairedGlobalOffPoleAssemblyMap shiftedLatticeKernelMap).domain :=
  intersectionOpenData pairedGlobalOffPoleAssemblyMap_holomorphic shiftedLatticeKernelMap_holomorphic

def latticeHalfShiftOriginalOn : DomainFunctions.Map :=
  onDomain pairedGlobalOffPoleAssemblyMap latticeHalfShiftProductOpenData.invariant (fun _ hz => hz.1)

def latticeHalfShiftShiftedOn : DomainFunctions.Map :=
  onDomain shiftedLatticeKernelMap latticeHalfShiftProductOpenData.invariant (fun _ hz => hz.2)

def latticeHalfShiftProductMap : DomainFunctions.Map :=
  productOn latticeHalfShiftOriginalOn latticeHalfShiftShiftedOn (fun _ hz => hz)

def latticeHalfShiftProductMap_holomorphic : Holomorphic latticeHalfShiftProductMap :=
  (pairedGlobalOffPoleAssemblyMap_holomorphic.onDomain latticeHalfShiftProductOpenData (fun _ hz => hz.1)).productOn
    (shiftedLatticeKernelMap_holomorphic.onDomain latticeHalfShiftProductOpenData (fun _ hz => hz.2)) (fun _ hz => hz)

def latticeHalfShiftProductErrorMap : DomainFunctions.Map :=
  compose (affine ⟨neg pairedRiccatiCenterConstant.val,neg_valid pairedRiccatiCenterConstant.property⟩
    ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩) latticeHalfShiftProductMap

def latticeHalfShiftProductErrorMap_holomorphic : Holomorphic latticeHalfShiftProductErrorMap :=
  (affine_holomorphic ⟨neg pairedRiccatiCenterConstant.val,neg_valid pairedRiccatiCenterConstant.property⟩
    ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩).compose latticeHalfShiftProductMap_holomorphic

theorem latticeHalfShiftProductError_differential_identity (z : Scalar)
    (hz : latticeHalfShiftProductErrorMap.domain z) :
    (latticeHalfShiftProductErrorMap_holomorphic.derivative z hz).val.Equiv
      (neg (mul (add (pairedGlobalOffPoleAssemblyMap.eval z (compose_inner_mem hz).1).val
        (shiftedLatticeKernelMap.eval z (compose_inner_mem hz).2).val)
        (latticeHalfShiftProductErrorMap.eval z hz).val)) := by
  let hm := compose_inner_mem hz
  let p := pairedGlobalOffPoleAssemblyMap.eval z hm.1
  let q := shiftedLatticeKernelMap.eval z hm.2
  let dp := pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z hm.1
  let dq := shiftedLatticeKernelMap_holomorphic.derivative z hm.2
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := add_valid dp.property (mul_valid p.property p.property))
    (hright := pairedRiccatiCenterConstant.property) (pairedGlobalOffPoleAssemblyMap_riccati_identity z hm.1)
  have hq := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := dq.property)
    (hright := sub_valid pairedRiccatiCenterConstant.property (mul_valid q.property q.property))
    (shiftedLatticeKernel_differential_identity z hm.2)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeHalfShiftProductErrorMap_holomorphic.derivative z hz).property)
    (hright := neg_valid (mul_valid (add_valid p.property q.property)
      (latticeHalfShiftProductErrorMap.eval z hz).property))
  let P := gridScalarValue p
  let Q := gridScalarValue q
  let DP := gridScalarValue dp
  let DQ := gridScalarValue dq
  let C := gridScalarValue pairedRiccatiCenterConstant
  change DP+P*P=C at hp
  change DQ=C-Q*Q at hq
  change 1*(DP*Q+P*DQ)= -((P+Q)*(-C+1*(P*Q)))
  rw [hq]
  grind only

theorem latticeHalfShiftProductError_local_mem (z : Scalar) (hz : latticeHalfShiftLocalDomain z)
    (hn : NonzeroBoxSearch.Nonzero z) : latticeHalfShiftProductErrorMap.domain z :=
  ⟨⟨latticeHalfShiftLocal_original_mem z hz hn,(latticeHalfShiftLocal_mem z hz).1⟩,trivial⟩

theorem latticeHalfShiftProductError_local_zero (z : Scalar) (hz : latticeHalfShiftLocalDomain z)
    (hn : NonzeroBoxSearch.Nonzero z) :
    (latticeHalfShiftProductErrorMap.eval z (latticeHalfShiftProductError_local_mem z hz hn)).val.Equiv zero := by
  let he := latticeHalfShiftProductError_local_mem z hz hn
  let p := pairedGlobalOffPoleAssemblyMap.eval z (compose_inner_mem he).1
  let q := shiftedLatticeKernelMap.eval z (compose_inner_mem he).2
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid p.property q.property)
    (hright := pairedRiccatiCenterConstant.property) (latticeHalfShiftLocal_product_identity z hz hn)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeHalfShiftProductErrorMap.eval z he).property) (hright := ofQComplex_valid _)
  let P := gridScalarValue p
  let Q := gridScalarValue q
  let C := gridScalarValue pairedRiccatiCenterConstant
  change P*Q=C at hp
  change -C+1*(P*Q)=(0:ScalarAlgebra.Value)
  rw [hp]
  grind only

end
end ComputableAnalysis.ModularForms
