import ComputableAnalysis.Basic

namespace ComputableAnalysis

/-! Concrete decimal digit-sum certificates for benchmark item 85. -/

theorem decimal_123_digit_sum :
    decimalDigitSum 123 = 6 := by
  native_decide

theorem decimal_123_divisible_by_three :
    3 ∣ 123 := by
  native_decide

theorem decimal_123_digit_sum_certificate :
    decimalDigitSum 123 % 3 = 0 /\ 123 % 3 = 0 := by
  native_decide

theorem decimal_124_not_divisible_by_three :
    ¬3 ∣ 124 := by
  native_decide

end ComputableAnalysis
