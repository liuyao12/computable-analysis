import ComputableAnalysis.FiniteCauchySchwarzList

/-!
# A worked three-coordinate Cauchy--Schwarz certificate

The vectors `(1,2,3)` and `(3,1,2)` are not proportional.  Their finite
certificate records the strict residual in the rational sum-of-squares form.
-/

namespace ComputableAnalysis

def cauchyThreeXs : List Rat := [1, 2, 3]
def cauchyThreeYs : List Rat := [3, 1, 2]

theorem cauchyThree_dot :
    rationalDot cauchyThreeXs cauchyThreeYs = 11 := by
  native_decide

theorem cauchyThree_sum_squares :
    rationalSumSquares cauchyThreeXs = 14 /\
      rationalSumSquares cauchyThreeYs = 14 := by
  native_decide

theorem cauchyThree_minor_residual :
    rationalMinorSquareSum cauchyThreeXs cauchyThreeYs = 75 := by
  native_decide

theorem cauchyThree_certificate :
    (rationalDot cauchyThreeXs cauchyThreeYs) ^ 2 <=
        rationalSumSquares cauchyThreeXs *
          rationalSumSquares cauchyThreeYs /\
      rationalSumSquares cauchyThreeXs * rationalSumSquares cauchyThreeYs -
          (rationalDot cauchyThreeXs cauchyThreeYs) ^ 2 =
        rationalMinorSquareSum cauchyThreeXs cauchyThreeYs := by
  constructor
  · exact rationalDot_cauchy_schwarz_of_length_eq (by native_decide)
  · native_decide

end ComputableAnalysis
