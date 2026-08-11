import ComputableAnalysis.FiniteCubicCompletion

/-!
# A worked finite cubic-completion certificate

The cubic `x^3 - 6x^2 + 11x - 6` is supplied with the rational root `1`.
The quotient discriminant is the rational square `1`, so the finite
completion theorem computes the two remaining roots `3` and `2`.
-/

namespace ComputableAnalysis

namespace Polynomial

theorem cubic_completion_example_roots :
    eval [-6, 11, -6, 1] 3 = 0 ∧
      eval [-6, 11, -6, 1] 2 = 0 := by
  have h := cubic_completion_roots_of_discriminant
    (-6 : Rat) 11 (-6) 1 1 1 (by native_decide) (by native_decide)
      (by native_decide)
  have hp : ((-(-6 + 1 * 1) + 1) / (2 * 1) : Rat) = 3 := by
    native_decide
  have hm : ((-(-6 + 1 * 1) - 1) / (2 * 1) : Rat) = 2 := by
    native_decide
  simpa only [hp, hm] using h

theorem cubic_completion_example_certificate :
    eval [-6, 11, -6, 1] 1 = 0 ∧
      eval [-6, 11, -6, 1] 2 = 0 ∧
        eval [-6, 11, -6, 1] 3 = 0 := by
  have h := cubic_completion_example_roots
  native_decide

end Polynomial

end ComputableAnalysis
