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

theorem decimal_321_digit_sum :
    decimalDigitSum 321 = 6 := by
  native_decide

theorem decimal_321_divisible_by_three :
    3 ∣ 321 := by
  native_decide

theorem decimal_321_digit_sum_certificate :
    decimalDigitSum 321 % 3 = 0 /\ 321 % 3 = 0 := by
  native_decide

theorem decimal_322_not_divisible_by_three :
    ¬3 ∣ 322 := by
  native_decide

theorem decimal_999_digit_sum :
    decimalDigitSum 999 = 27 := by
  native_decide

theorem decimal_999_divisible_by_three :
    3 ∣ 999 := by
  native_decide

theorem decimal_1000_not_divisible_by_three :
    ¬3 ∣ 1000 := by
  native_decide

theorem decimal_123456_digit_sum :
    decimalDigitSum 123456 = 21 := by
  native_decide

theorem decimal_123456_divisible_by_three :
    3 ∣ 123456 := by
  native_decide

theorem decimal_123456_digit_sum_certificate :
    decimalDigitSum 123456 % 3 = 0 /\ 123456 % 3 = 0 := by
  native_decide

theorem decimal_123457_not_divisible_by_three :
    ¬3 ∣ 123457 := by
  native_decide

end ComputableAnalysis
