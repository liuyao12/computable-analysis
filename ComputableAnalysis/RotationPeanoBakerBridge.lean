import ComputableAnalysis.RotationSeries

/-!
# The factorial rotation centers as Peano--Baker matrices

This is the finite algebraic part of the Euler route.  The complex factorial
prefix at a rational angle and the constant-coefficient Peano--Baker partial
matrix for the rotation generator are literally the same cosine/sine
polynomial.  No continuous ODE solution or geometric endpoint identification
is used here.
-/

namespace ComputableAnalysis

namespace RotationPeanoBakerBridge

/-- The finite complex center used by the factorial rotation enclosure is the
first-column complex form of the corresponding constant-coefficient
Peano--Baker partial matrix. -/
theorem rotationCenter_eq_constantPeanoBakerPartial
    (T : Rat) (n : Nat) :
    LinearODE.constantPeanoBakerSimplexPartial
        LinearODE.RotationSystem.generator T
        (RotationSeries.rotationTailTerms T n) =
      LinearODE.matrixAdd
        (LinearODE.matrixScale (RotationSeries.rotationCenter T n).re
          (LinearODE.matrixIdentity 2))
        (LinearODE.matrixScale (RotationSeries.rotationCenter T n).im
          LinearODE.RotationSystem.generator) := by
  unfold RotationSeries.rotationTailTerms
  simpa [RotationSeries.rotationCenter, RotationSeries.complexPrefix] using
    (LinearODE.RotationSystem.simplexPartial_even_split T
      (RotationSeries.rotationTailStart T + n))

/-- The same finite rotation center is the even factorial prefix of the
complex exponential at the rational imaginary input. -/
theorem rotationCenter_eq_expPartial
    (T : Rat) (n : Nat) :
    RotationSeries.rotationCenter T n =
      ComplexSeries.expPartial (RotationSeries.imaginaryAxis T)
        (RotationSeries.rotationTailTerms T n) :=
  RotationSeries.rotationCenter_eq_expPartial T n

end RotationPeanoBakerBridge

end ComputableAnalysis
