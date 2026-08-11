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

end ComputableAnalysis
