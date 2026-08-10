import ComputableAnalysis.CauchyPi
import ComputableAnalysis.Logarithm

/-!
# Finite integration-by-parts and substitution computations of pi

The two raw algorithms in this module are the executable witnesses behind the
blueprint's supplied arctangent integration-by-parts formula.  They use a
literal reciprocal integral for the logarithmic endpoint, or its certified
square-pullback form.  Neither theorem identifies that endpoint with a future
canonical inverse-exponential logarithm.
-/

namespace ComputableAnalysis

namespace LogarithmicPi

/-- The supplied arctangent integration-by-parts computation with the
endpoint retained as the literal reciprocal integral on `[1,2]`. -/
def reciprocalRaw : RealRaw := Logarithm.piTriangleLogReciprocalIntegral

theorem reciprocalRaw_valid : reciprocalRaw.Valid :=
  Logarithm.piTriangleLogReciprocalIntegral_valid

theorem reciprocalRaw_width_le (n : Nat) :
    (reciprocalRaw.compute n).width <= 52 * (1 / (((2 ^ n : Nat) : Rat))) := by
  exact Logarithm.piTriangleLogReciprocalIntegral_compute_width_le n

/-- The finite integration-by-parts computation reaches the geometric
circle-area representative of pi through the unit arctangent endpoint. -/
theorem reciprocalRaw_equiv_piCircleArea : reciprocalRaw.Equiv piCircleArea := by
  exact RealRaw.equiv_trans reciprocalRaw_valid
    ArctanGeometry.four_arctanGeom_one_valid
    CauchyPi.piCircleArea_valid
    Logarithm.piTriangleLogReciprocalIntegral_equiv_four_arctanGeom_one
    ArctanGeometry.four_arctanGeom_one_equiv_piCircleArea

/-- The same endpoint, computed by the finite square substitution
`t = x^2` rather than by the reciprocal integral directly. -/
def squareSubstitutionRaw : RealRaw :=
  Logarithm.piTriangleLogSquareSubstitutionIntegral

theorem squareSubstitutionRaw_valid : squareSubstitutionRaw.Valid :=
  Logarithm.piTriangleLogSquareSubstitutionIntegral_valid

theorem squareSubstitutionRaw_width_le (n : Nat) :
    (squareSubstitutionRaw.compute n).width <=
      56 * (1 / (((2 ^ n : Nat) : Rat))) := by
  exact Logarithm.piTriangleLogSquareSubstitutionIntegral_compute_width_le n

/-- The square substitution and reciprocal-integral endpoint calculations
agree before either is compared with geometric pi. -/
theorem squareSubstitutionRaw_equiv_reciprocalRaw :
    squareSubstitutionRaw.Equiv reciprocalRaw := by
  exact Logarithm.piTriangleLogSquareSubstitutionIntegral_equiv_piTriangleLogReciprocalIntegral

theorem squareSubstitutionRaw_equiv_piCircleArea :
    squareSubstitutionRaw.Equiv piCircleArea := by
  exact RealRaw.equiv_trans squareSubstitutionRaw_valid reciprocalRaw_valid
    CauchyPi.piCircleArea_valid squareSubstitutionRaw_equiv_reciprocalRaw
    reciprocalRaw_equiv_piCircleArea

end LogarithmicPi

end ComputableAnalysis
