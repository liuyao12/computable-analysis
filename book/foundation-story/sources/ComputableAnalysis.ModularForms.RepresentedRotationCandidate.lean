import ComputableAnalysis.ModularForms.RotationExponentialAgreement
import ComputableAnalysis.RotationLift

/-! Error against the actual midpoint factorial candidate of a represented
rotation. No quarter-turn value is assumed. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem imaginaryAxis_center (x : RealRaw) (n : Nat) :
    ((ComplexRaw.imaginaryAxis x).compute n).center =
      RotationSeries.imaginaryAxis (x.compute n).midpoint := by
  rw [RotationSeries.imaginaryAxis_coordinates]
  change (⟨((-0)+(-0))/2, ((x.compute n).lo+(x.compute n).hi)/2⟩ : QComplex) =
    ⟨0,(x.compute n).midpoint⟩
  congr 1
  · decide +kernel

theorem represented_rotation_prefix_compute (A : RotationLift.HalfPiInput) (n stage : Nat) :
    (ScalarSeries.block (LocalODE.seriesTerm exponentialCoefficients
      (ofQComplex (((ComplexRaw.imaginaryAxis A.raw).compute n).center))) 0
      (RotationSeries.uniformRotationTailTerms n)).compute stage =
      QBox.point (RotationSeries.uniformRotationCenter (A.raw.compute n).midpoint n) := by
  rw [imaginaryAxis_center]
  exact uniform_rotation_candidate_compute _ n stage

theorem represented_rotation_candidate_error (A : RotationLift.HalfPiInput) (n : Nat) :
    Small (sub (RotationLift.HalfPiInput.rotation A)
      (ofQComplex (RotationSeries.uniformRotationCenter (A.raw.compute n).midpoint n)))
      (centerError (RotationLift.HalfPiInput.rotation A) n) := by
  have hv := RotationLift.HalfPiInput.rotation_valid A
  have hr : 0 ≤ RotationSeries.uniformRotationTailRadius n :=
    Rat.mul_nonneg (by decide +kernel)
      (RationalMajorant.factorialTailTerm_nonneg (by decide +kernel) _)
  have hp : (QBox.point (RotationSeries.uniformRotationCenter (A.raw.compute n).midpoint n)).NestedIn
      ((RotationLift.HalfPiInput.rotationCandidate A).compute n) := by
    simp only [RotationLift.HalfPiInput.rotationCandidate_compute,
      RotationSeries.uniformRotationBox, QBox.NestedIn, QBox.point, QComplex.le_def]
    grind
  have hcontained := QBox.nested_trans hp
    (RotationLift.HalfPiInput.rotation_contains_current_candidate A n)
  apply point_in_box_error _ hv _ n _ hcontained
  · have hh := (hv.1 n).2
    unfold centerError
    grind
  · have hw := (hv.1 n).1
    unfold centerError
    grind

theorem represented_rotation_candidate_error_shrinks (A : RotationLift.HalfPiInput) :
    ShrinksToZero (centerError (RotationLift.HalfPiInput.rotation A)) :=
  centerError_shrinks _ (RotationLift.HalfPiInput.rotation_valid A)

end ComputableAnalysis.ModularForms
