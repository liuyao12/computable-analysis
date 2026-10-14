import ComputableAnalysis.ModularForms.ExponentialRationalPrefix
import ComputableAnalysis.RotationSeries
import ComputableAnalysis.ModularForms.RationalCenterApproximation

/-! The actual finite rotation candidates are represented factorial prefixes
at imaginary inputs. Infinite evaluator agreement is a separate step. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem rotation_prefix_compute (T : Rat) (pairs stage : Nat) :
    (ScalarSeries.block (LocalODE.seriesTerm exponentialCoefficients
      (ofQComplex (RotationSeries.imaginaryAxis T))) 0 (2*pairs)).compute stage =
      QBox.point (RotationSeries.complexPrefix T pairs) := by
  rw [rational_exponential_prefix_compute,
    ComplexExponentialApproximation.expPrefix_eq_complexSeries_expPartial,
    RotationSeries.expPartial_imaginary_even_split]

theorem uniform_rotation_candidate_compute (T : Rat) (n stage : Nat) :
    (ScalarSeries.block (LocalODE.seriesTerm exponentialCoefficients
      (ofQComplex (RotationSeries.imaginaryAxis T))) 0
      (RotationSeries.uniformRotationTailTerms n)).compute stage =
      QBox.point (RotationSeries.uniformRotationCenter T n) := by
  exact rotation_prefix_compute T (RotationSeries.uniformRotationTailStart+n) stage

theorem uniform_rotation_prefix_error (T : Rat) (hT : qabs T ≤ 2) (n : Nat) :
    Small (sub (RotationSeries.uniformRotationExpRaw T)
      (ofQComplex (RotationSeries.uniformRotationCenter T n)))
      (centerError (RotationSeries.uniformRotationExpRaw T) n) := by
  have hv := RotationSeries.uniformRotationExpRaw_valid T hT
  have hr : 0 ≤ RotationSeries.uniformRotationTailRadius n :=
    Rat.mul_nonneg (by decide +kernel)
      (RationalMajorant.factorialTailTerm_nonneg (by decide +kernel) _)
  have hp : (QBox.point (RotationSeries.uniformRotationCenter T n)).NestedIn
      ((RotationSeries.uniformRotationExpRaw T).compute n) := by
    simp only [RotationSeries.uniformRotationExpRaw_compute, RotationSeries.uniformRotationBox,
      QBox.NestedIn, QBox.point, QComplex.le_def]
    grind
  apply point_in_box_error _ hv _ n _ hp
  · have hh := (hv.1 n).2
    unfold centerError
    grind
  · have hw := (hv.1 n).1
    unfold centerError
    grind

theorem uniform_rotation_prefix_error_shrinks (T : Rat) (hT : qabs T ≤ 2) :
    ShrinksToZero (centerError (RotationSeries.uniformRotationExpRaw T)) :=
  centerError_shrinks _ (RotationSeries.uniformRotationExpRaw_valid T hT)

end ComputableAnalysis.ModularForms
