import ComputableAnalysis.ModularForms.GeometricPiNonvanishing
import ComputableAnalysis.ModularForms.CMFourierDiscriminantNonvanishing163
import ComputableAnalysis.ModularForms.ScalarNonvanishingAlgebra

/-! The actual CM lattice discriminant is nonzero, justifying the CM j evaluator. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- The actual CM lattice discriminant has a proved nonzero value. -/
theorem cmDiscriminant163_nonzero : NonzeroBoxSearch.Nonzero cmDiscriminant163 := by
  let P : Scalar := ⟨LocalODE.power geometricPiScalar.val 12,
    LocalODE.power_valid _ geometricPiScalar.property 12⟩
  let D : Scalar := ⟨mul P.val cmFourierDiscriminant163.val,
    mul_valid P.property cmFourierDiscriminant163.property⟩
  have hp : NonzeroBoxSearch.Nonzero P := scalar_power_nonzero _ geometricPiScalar_nonzero 12
  have hd : NonzeroBoxSearch.Nonzero D := scalar_mul_nonzero _ _ hp cmFourierDiscriminant163_nonzero
  have hs := scalar_scale_nonzero D hd 4096 (by decide +kernel)
  exact (NonzeroBoxSearch.nonzero_congr cmDiscriminant163
    ⟨scaleRat 4096 D.val,scaleRat_valid D.property⟩ cmDiscriminant163_normalized_fourier).mpr hs

/-- The actual lattice j evaluator is defined at the constructed CM point. -/
theorem latticeJMap_cm_domain : latticeJMap.domain cmScalar163 :=
  latticeJMap_cm_domain_iff.mpr cmDiscriminant163_nonzero

/-- The actual CM j value, with its denominator justified by proved nonvanishing. -/
def cmJValue163 : Scalar := latticeJMap.eval cmScalar163 latticeJMap_cm_domain

/-- The constructed CM j value satisfies the actual lattice invariant identity. -/
theorem cmJValue163_discriminant_product :
    (mul cmJValue163.val cmDiscriminant163.val).Equiv
      (mul (ofQComplex ⟨1728,0⟩) (latticeG2CubeMap.eval cmScalar163 cmPoint163_upper).val) :=
  equiv_trans (mul_valid cmJValue163.property cmDiscriminant163.property)
    (mul_valid cmJValue163.property (latticeDiscriminantMap.eval cmScalar163 cmPoint163_upper).property)
    (mul_valid (ofQComplex_valid _) (latticeG2CubeMap.eval cmScalar163 cmPoint163_upper).property)
    (mul_equiv cmJValue163.property cmJValue163.property cmDiscriminant163.property
      (latticeDiscriminantMap.eval cmScalar163 cmPoint163_upper).property
      (equiv_refl _ cmJValue163.property) (equiv_symm latticeDiscriminantMap_cm_agreement))
    (latticeJMap_discriminant_product cmScalar163 latticeJMap_cm_domain)

end ComputableAnalysis.ModularForms
