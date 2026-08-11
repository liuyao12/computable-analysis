import ComputableAnalysis.FiniteCauchySchwarzList

/-!
# A worked six-coordinate Cauchy--Schwarz certificate

The vectors `(1,2,3,4,5,6)` and `(6,5,4,3,2,1)` provide a larger finite
list-level witness with an explicit sum-of-squares residual.
-/

namespace ComputableAnalysis

def cauchySixXs : List Rat := [1, 2, 3, 4, 5, 6]
def cauchySixYs : List Rat := [6, 5, 4, 3, 2, 1]

theorem cauchySix_dot :
    rationalDot cauchySixXs cauchySixYs = 56 := by
  native_decide

theorem cauchySix_sum_squares :
    rationalSumSquares cauchySixXs = 91 /\
      rationalSumSquares cauchySixYs = 91 := by
  native_decide

theorem cauchySix_minor_residual :
    rationalMinorSquareSum cauchySixXs cauchySixYs = 5145 := by
  native_decide

theorem cauchySix_certificate :
    (rationalDot cauchySixXs cauchySixYs) ^ 2 <=
        rationalSumSquares cauchySixXs * rationalSumSquares cauchySixYs /\
      rationalSumSquares cauchySixXs * rationalSumSquares cauchySixYs -
          (rationalDot cauchySixXs cauchySixYs) ^ 2 =
        rationalMinorSquareSum cauchySixXs cauchySixYs := by
  constructor
  · exact rationalDot_cauchy_schwarz_of_length_eq (by native_decide)
  · native_decide

end ComputableAnalysis
