import ComputableAnalysis.FiniteCauchySchwarzList

/-!
# A worked four-coordinate Cauchy--Schwarz certificate

The vectors `(1,2,3,4)` and `(4,3,2,1)` give a concrete strict finite
certificate with an explicit sum-of-squares residual.
-/

namespace ComputableAnalysis

def cauchyFourXs : List Rat := [1, 2, 3, 4]
def cauchyFourYs : List Rat := [4, 3, 2, 1]

theorem cauchyFour_dot :
    rationalDot cauchyFourXs cauchyFourYs = 20 := by
  native_decide

theorem cauchyFour_sum_squares :
    rationalSumSquares cauchyFourXs = 30 /\
      rationalSumSquares cauchyFourYs = 30 := by
  native_decide

theorem cauchyFour_minor_residual :
    rationalMinorSquareSum cauchyFourXs cauchyFourYs = 500 := by
  native_decide

theorem cauchyFour_certificate :
    (rationalDot cauchyFourXs cauchyFourYs) ^ 2 <=
        rationalSumSquares cauchyFourXs * rationalSumSquares cauchyFourYs /\
      rationalSumSquares cauchyFourXs * rationalSumSquares cauchyFourYs -
          (rationalDot cauchyFourXs cauchyFourYs) ^ 2 =
        rationalMinorSquareSum cauchyFourXs cauchyFourYs := by
  constructor
  · exact rationalDot_cauchy_schwarz_of_length_eq (by native_decide)
  · native_decide

end ComputableAnalysis
