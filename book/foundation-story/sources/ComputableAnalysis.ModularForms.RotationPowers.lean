import ComputableAnalysis.ModularForms.RepresentedRotationAgreement
import ComputableAnalysis.ModularForms.ExponentialPowers

/-! Scaling the imaginary angle evaluates to a power of its actual rotation.
The exact geometric quarter-turn value is still a separate theorem. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem entireExponential_rotation_multiple (A : RotationLift.HalfPiInput) (n : Nat) :
    (entireExponentialValue
      ⟨scaleRat (n : Rat) (ComplexRaw.imaginaryAxis A.raw),
        scaleRat_valid (imaginaryAxis_valid A.valid)⟩).val.Equiv
      (LocalODE.power (RotationLift.HalfPiInput.rotation A) n) := by
  let z : Scalar := ⟨ComplexRaw.imaginaryAxis A.raw,imaginaryAxis_valid A.valid⟩
  have h (k : Nat) : (LocalODE.power (entireExponentialValue z).val k).Equiv
      (LocalODE.power (RotationLift.HalfPiInput.rotation A) k) := by
    induction k with
    | zero => exact equiv_refl _ (ofQComplex_valid _)
    | succ k ih =>
      exact mul_equiv
        (LocalODE.power_valid _ (entireExponentialValue z).property k)
        (LocalODE.power_valid _ (RotationLift.HalfPiInput.rotation_valid A) k)
        (entireExponentialValue z).property (RotationLift.HalfPiInput.rotation_valid A)
        ih (entireExponential_represented_rotation A)
  exact equiv_trans
    (entireExponentialValue ⟨scaleRat (n : Rat) z.val,scaleRat_valid z.property⟩).property
    (LocalODE.power_valid _ (entireExponentialValue z).property n)
    (LocalODE.power_valid _ (RotationLift.HalfPiInput.rotation_valid A) n)
    (entireExponential_nat_multiple z n) (h n)

end ComputableAnalysis.ModularForms
