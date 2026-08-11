import ComputableAnalysis.Differential
import ComputableAnalysis.AlgebraicFunctions

/-!
# A worked finite cubic Mean Value certificate

On `[0,1]`, the cubic secant slope is exactly `1`.  The midpoint formula
records it as the derivative value `3/4` plus the explicit finite remainder
`1/4`; no intermediate real point or limiting theorem is introduced.
-/

namespace ComputableAnalysis

open ExactFunction

/-! The cubic has a non-rational intermediate MVT point on `[0,1]`.
Its secant slope is `1`, so the normalized derivative target is `1/3` for
the square branch.  The existing certified square-root search therefore gives
an executable enclosure of the intermediate point, rather than requiring an
exact rational witness. -/

def cubicUnitNormalizedDerivativeAverage : Rat := 1 / 3

theorem cubicUnitNormalizedDerivativeAverage_in_unit :
    inDomainInterval 0 1 cubicUnitNormalizedDerivativeAverage := by
  unfold cubicUnitNormalizedDerivativeAverage inDomainInterval
  native_decide

theorem cubicUnit_secant_eq_three_mul_normalizedDerivativeAverage :
    differenceQuotient cube 0 (1 - 0) =
      3 * cubicUnitNormalizedDerivativeAverage := by
  unfold cubicUnitNormalizedDerivativeAverage differenceQuotient cube
  native_decide

def cubicUnit_mvt_bisection_search :
    InverseBisectionSearch squareOnUnit_invertible
      (squareOnUnitRationalTarget
        cubicUnitNormalizedDerivativeAverage
        cubicUnitNormalizedDerivativeAverage_in_unit) :=
  sqrtOnUnitBisectionSearch
    cubicUnitNormalizedDerivativeAverage
    cubicUnitNormalizedDerivativeAverage_in_unit

theorem cubic_secant_unit_interval :
    differenceQuotient cube 0 (1 - 0) = 1 := by
  native_decide

theorem cubic_midpoint_secant_unit_interval :
    differenceQuotient cube 0 (1 - 0) =
      3 * (((0 : Rat) + 1) / 2) ^ 2 + (1 - 0) ^ 2 / 4 := by
  exact cube_midpoint_secant (by native_decide)

theorem cubic_midpoint_secant_unit_interval_remainder :
    3 * (((0 : Rat) + 1) / 2) ^ 2 + (1 - 0) ^ 2 / 4 = 1 := by
  native_decide

theorem cubic_mvt_unit_interval_certificate :
    differenceQuotient cube 0 (1 - 0) = 1 ∧
      3 * (((0 : Rat) + 1) / 2) ^ 2 = 3 / 4 ∧
      (1 - 0) ^ 2 / 4 = 1 / 4 := by
  native_decide

/-! A signed-domain checkpoint on `[-1,1]`. -/

theorem cubic_secant_signed_interval :
    differenceQuotient cube (-1 : Rat) (1 - (-1)) = 1 := by
  native_decide

theorem cubic_mvt_signed_interval_certificate :
    differenceQuotient cube (-1 : Rat) (1 - (-1)) = 1 /\
      (0 : Rat) <= 3 * (-1) ^ 2 /\
      3 * 1 ^ 2 <= 3 := by
  native_decide

/-! A genuine rational intermediate-point witness on a positive interval.

The cubic derivative `3 * x^2` is monotone on `[2,11]`, and the secant
slope happens to be attained at the rational point `7`. -/

theorem cubic_secant_rational_witness_interval :
    differenceQuotient cube (2 : Rat) (11 - 2) = 147 := by
  native_decide

theorem cubic_mvt_rational_witness_interval :
    (2 : Rat) < 7 /\
      (7 : Rat) < 11 /\
      differenceQuotient cube 2 (11 - 2) = 3 * 7 ^ 2 := by
  simpa [Rat.mul_assoc, Rat.pow_succ, Rat.pow_zero] using
    (cube_secant_supplied_mvt_witness
      (a := (2 : Rat)) (b := 11) (t := 7)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide))

end ComputableAnalysis
