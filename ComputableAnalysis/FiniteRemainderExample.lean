import ComputableAnalysis.Polynomial

/-!
# A worked factor/remainder certificate

For `p(x)=x^2-3x+2`, the supplied root `1` gives the exact finite factor
identity at the sample point `4`.  The evaluation and quotient are both
checked over rationals.
-/

namespace ComputableAnalysis

namespace Polynomial

theorem quadratic_remainder_example_root :
    eval [2, -3, 1] 1 = 0 := by
  native_decide

theorem quadratic_remainder_example_value :
    eval [2, -3, 1] 4 = 6 := by
  native_decide

theorem quadratic_remainder_example_factor :
    eval [2, -3, 1] 4 =
      (4 - 1) * ((1 : Rat) * 4 + (-3) + 1 * 1) := by
  exact quadratic_factor_of_root quadratic_remainder_example_root

theorem quadratic_remainder_example_certificate :
    eval [2, -3, 1] 4 = 6 ∧
      eval [2, -3, 1] 4 =
        (4 - 1) * ((1 : Rat) * 4 + (-3) + 1 * 1) := by
  exact ⟨quadratic_remainder_example_value,
    quadratic_remainder_example_factor⟩

end Polynomial

end ComputableAnalysis
