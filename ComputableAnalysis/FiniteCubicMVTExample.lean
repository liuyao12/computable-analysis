import ComputableAnalysis.Differential

/-!
# A worked finite cubic Mean Value certificate

On `[0,1]`, the cubic secant slope is exactly `1`.  The midpoint formula
records it as the derivative value `3/4` plus the explicit finite remainder
`1/4`; no intermediate real point or limiting theorem is introduced.
-/

namespace ComputableAnalysis

open ExactFunction

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

end ComputableAnalysis
