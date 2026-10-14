import ComputableAnalysis.ModularForms.RotationPowers
import ComputableAnalysis.ModularForms.Nome

/-! Relating the nome slope to the actual geometric rotation. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem nomeSlope_exponential_rotation_fourth :
    (entireExponentialValue nomeSlope).val.Equiv
      (LocalODE.power GeometricPiRotation.rotation 4) := by
  let x : Scalar := ⟨scaleRat ((4 : Nat) : Rat) GeometricPiRotation.imaginaryHalf,
    scaleRat_valid GeometricPiRotation.imaginaryHalf_valid⟩
  have hx : nomeSlope.val.Equiv x.val := by
    have hc : ((4 : Nat) : Rat) = (4 : Rat) := by decide +kernel
    intro n
    apply (compareAt_overlap_iff _ _ n n).mpr
    change (QBox.scaleRat 4 (GeometricPiRotation.imaginaryHalf.compute n)).Overlaps
      (QBox.scaleRat ((4 : Nat) : Rat) (GeometricPiRotation.imaginaryHalf.compute n))
    rw [hc]
    exact (compareAt_overlap_iff nomeSlope.val nomeSlope.val n n).mp
      (equiv_refl nomeSlope.val nomeSlope.property n)
  exact equiv_trans (entireExponentialValue nomeSlope).property
    (entireExponentialValue x).property
    (LocalODE.power_valid _ GeometricPiRotation.rotation_valid 4)
    (entireExponentialValue_congr nomeSlope x hx)
    (entireExponential_rotation_multiple GeometricPiRotation.halfPiInput 4)

theorem nome_translate_one (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (nome.eval ⟨translate 1 z.val,translate_valid 1 z.property⟩ (translate_mem 1 hz)).val.Equiv
      (mul (nome.eval z hz).val (LocalODE.power GeometricPiRotation.rotation 4)) := by
  let t : Scalar := ⟨translate 1 z.val,translate_valid 1 z.property⟩
  have ht : InUpperHalfPlane t.val := translate_mem 1 hz
  let a := nomeExponentMap.eval z hz
  let b : Scalar := ⟨add a.val nomeSlope.val,add_valid a.property nomeSlope.property⟩
  have heq : (nomeExponentMap.eval t ht).val.Equiv b.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (nomeExponentMap.eval t ht).property) (hright := b.property)
    change ComplexRawQuotient.ofRaw nomeSlope.val nomeSlope.property *
      (ComplexRawQuotient.ofRaw z.val z.property + ComplexRawQuotient.ofQComplex ⟨1,0⟩) =
      ComplexRawQuotient.ofRaw nomeSlope.val nomeSlope.property * ComplexRawQuotient.ofRaw z.val z.property +
      ComplexRawQuotient.ofRaw nomeSlope.val nomeSlope.property
    have h1 : ComplexRawQuotient.ofQComplex ⟨1,0⟩ = (1 : ScalarAlgebra.Value) :=
      rfl
    rw [h1]
    grind
  have hprod := entireExponential_addition a nomeSlope
  have hmul := mul_equiv (entireExponentialValue a).property (entireExponentialValue a).property
    (entireExponentialValue nomeSlope).property
    (LocalODE.power_valid _ GeometricPiRotation.rotation_valid 4)
    (equiv_refl _ (entireExponentialValue a).property) nomeSlope_exponential_rotation_fourth
  exact equiv_trans (nome.eval t ht).property (entireExponentialValue b).property
    (mul_valid (entireExponentialValue a).property (LocalODE.power_valid _ GeometricPiRotation.rotation_valid 4))
    (entireExponentialValue_congr _ b heq)
    (equiv_trans (entireExponentialValue b).property
      (mul_valid (entireExponentialValue a).property (entireExponentialValue nomeSlope).property)
      (mul_valid (entireExponentialValue a).property (LocalODE.power_valid _ GeometricPiRotation.rotation_valid 4))
      (equiv_symm hprod) hmul)

end ComputableAnalysis.ModularForms
