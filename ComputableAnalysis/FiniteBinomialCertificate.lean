import ComputableAnalysis.Series

namespace ComputableAnalysis

/-! A concrete finite binomial-theorem certificate for benchmark item 44. -/

theorem binomial_stage5_two_one :
    Series.binomialSum 5 2 1 6 = 3 ^ 5 := by
  rw [Series.binomialSum_eq_pow]
  native_decide

theorem binomial_stage5_two_one_value :
    Series.binomialSum 5 2 1 6 = 243 := by
  rw [binomial_stage5_two_one]
  native_decide

theorem binomial_stage5_two_one_certificate :
    Series.binomialSum 5 2 1 6 = 243 /\
      (3 : Rat) ^ 5 = 243 := by
  constructor
  · exact binomial_stage5_two_one_value
  · native_decide

theorem binomial_stage8_two_one :
    Series.binomialSum 8 2 1 9 = 6561 := by
  rw [Series.binomialSum_eq_pow]
  native_decide

theorem binomial_stage10_two_one :
    Series.binomialSum 10 2 1 11 = 59049 := by
  rw [Series.binomialSum_eq_pow]
  native_decide

theorem binomial_stage12_two_one :
    Series.binomialSum 12 2 1 13 = 531441 := by
  rw [Series.binomialSum_eq_pow]
  native_decide

theorem binomial_stage16_two_one :
    Series.binomialSum 16 2 1 17 = 43046721 := by
  rw [Series.binomialSum_eq_pow]
  native_decide

theorem binomial_stage20_two_one :
    Series.binomialSum 20 2 1 21 = 3486784401 := by
  rw [Series.binomialSum_eq_pow]
  native_decide

theorem binomial_stage6_two_three :
    Series.binomialSum 6 2 3 7 = 5 ^ 6 := by
  rw [Series.binomialSum_eq_pow]
  native_decide

theorem binomial_stage6_two_three_value :
    Series.binomialSum 6 2 3 7 = 15625 := by
  rw [binomial_stage6_two_three]
  native_decide

theorem binomial_stage8_two_three :
    Series.binomialSum 8 2 3 9 = 390625 := by
  rw [Series.binomialSum_eq_pow]
  native_decide

theorem binomial_stage5_four_three :
    Series.binomialSum 5 4 3 6 = 16807 := by
  rw [Series.binomialSum_eq_pow]
  native_decide

end ComputableAnalysis
