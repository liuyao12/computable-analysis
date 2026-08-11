import ComputableAnalysis.FiniteNBallVolume
import ComputableAnalysis.FiniteExponentialTaylor
import ComputableAnalysis.ExpProofs

/-!
# Finite Gaussian integral prefixes

This is the bounded, finite layer of the Gaussian route.  The integrand is the
even Taylor prefix for `exp (-x^2)`, and each monomial is integrated exactly
over `[-radius,radius]`.  It is not yet an improper integral over the line.
-/

namespace ComputableAnalysis

def gaussianEvenIntegralPrefix (terms : Nat) (radius : Rat) : Rat :=
  (List.range terms).foldl
    (fun acc k =>
      acc + 2 * FormalPowerSeries.expCoeff k * (-1 : Rat) ^ k *
        radius ^ (2 * k + 1) / ((2 * k + 1 : Nat) : Rat)) 0

theorem gaussianEvenIntegralPrefix_zero (radius : Rat) :
    gaussianEvenIntegralPrefix 0 radius = 0 := by
  rfl

theorem gaussianEvenIntegralPrefix_stage_four :
    gaussianEvenIntegralPrefix 4 1 = 52 / 35 := by
  native_decide

theorem gaussianEvenIntegralPrefix_stage_six :
    gaussianEvenIntegralPrefix 6 1 = 31049 / 20790 := by
  native_decide

theorem gaussianEvenIntegralPrefix_stage_eight :
    gaussianEvenIntegralPrefix 8 1 = 1009219 / 675675 := by
  native_decide

theorem gaussianEvenIntegralPrefix_stage_six_minus_four :
    gaussianEvenIntegralPrefix 6 1 - gaussianEvenIntegralPrefix 4 1 =
      23 / 2970 := by
  rw [gaussianEvenIntegralPrefix_stage_six,
    gaussianEvenIntegralPrefix_stage_four]
  native_decide

theorem gaussianEvenIntegralPrefix_stage_four_nonnegative :
    0 <= gaussianEvenIntegralPrefix 4 1 := by
  rw [gaussianEvenIntegralPrefix_stage_four]
  native_decide

/-! A finite reciprocal-square tail, suitable for transporting a supplied
pointwise Gaussian domination certificate. -/

def reciprocalSquareTailPartial (cutoff : Rat) : Nat -> Rat
  | 0 => 0
  | terms + 1 =>
      reciprocalSquareTailPartial cutoff terms +
        1 / (cutoff + (terms + 1 : Nat)) ^ 2

theorem reciprocalSquareTailPartial_stage_four :
    reciprocalSquareTailPartial 1 4 = 1669 / 3600 := by
  native_decide

theorem reciprocalSquareTailPartial_stage_four_below_one :
    reciprocalSquareTailPartial 1 4 < 1 := by
  rw [reciprocalSquareTailPartial_stage_four]
  native_decide

theorem reciprocalSquareTailPartial_stage_six :
    reciprocalSquareTailPartial 1 6 = 90281 / 176400 := by
  native_decide

theorem reciprocalSquareTailPartial_stage_eight :
    reciprocalSquareTailPartial 1 8 = 3427741 / 6350400 := by
  native_decide

theorem reciprocalSquareTailPartial_stage_eight_below_one :
    reciprocalSquareTailPartial 1 8 < 1 := by
  rw [reciprocalSquareTailPartial_stage_eight]
  native_decide

/-! A concrete pointwise Gaussian tail witness from the project's certified
power-series exponential box. -/

theorem expPowerSeries_neg_four_stage_twenty_upper :
    ((expPowerSeries (-4 : Rat)).compute 20).hi <= 1 / 4 := by
  native_decide

theorem expPowerSeries_neg_nine_stage_twenty_upper :
    ((expPowerSeries (-9 : Rat)).compute 20).hi <= 1 / 9 := by
  native_decide

theorem expPowerSeries_neg_sixteen_stage_twenty_upper :
    ((expPowerSeries (-16 : Rat)).compute 20).hi <= 1 / 16 := by
  native_decide

theorem expPowerSeries_neg_twenty_five_stage_twenty_upper :
    ((expPowerSeries (-25 : Rat)).compute 20).hi <= 1 / 25 := by
  native_decide

theorem gaussianTailPointLadder_stage_twenty :
    ((expPowerSeries (-4 : Rat)).compute 20).hi <= 1 / 4 /\
      ((expPowerSeries (-9 : Rat)).compute 20).hi <= 1 / 9 /\
      ((expPowerSeries (-16 : Rat)).compute 20).hi <= 1 / 16 := by
  exact ⟨expPowerSeries_neg_four_stage_twenty_upper,
    expPowerSeries_neg_nine_stage_twenty_upper,
    expPowerSeries_neg_sixteen_stage_twenty_upper⟩

def gaussianTailBoxUpper (x : Rat) (stage : Nat) : Rat :=
  ((expPowerSeries (-(x * x))).compute stage).hi

theorem gaussianTailBoxUpper_stage_twenty_ladder :
    gaussianTailBoxUpper 2 20 <= 1 / 4 /\
      gaussianTailBoxUpper 3 20 <= 1 / 9 /\
      gaussianTailBoxUpper 4 20 <= 1 / 16 := by
  native_decide

theorem gaussianTailBoxUpper_stage_twenty_ladder_four :
    gaussianTailBoxUpper 2 20 <= 1 / 4 /\
      gaussianTailBoxUpper 3 20 <= 1 / 9 /\
      gaussianTailBoxUpper 4 20 <= 1 / 16 /\
      gaussianTailBoxUpper 5 20 <= 1 / 25 := by
  native_decide

theorem gaussianTailBoxUpper_stage_twenty_ladder_eight :
    gaussianTailBoxUpper 2 20 <= 1 / 4 /\
      gaussianTailBoxUpper 3 20 <= 1 / 9 /\
      gaussianTailBoxUpper 4 20 <= 1 / 16 /\
      gaussianTailBoxUpper 5 20 <= 1 / 25 /\
      gaussianTailBoxUpper 6 100 <= 1 / 36 /\
      gaussianTailBoxUpper 7 100 <= 1 / 49 /\
      gaussianTailBoxUpper 8 100 <= 1 / 64 := by
  native_decide

theorem gaussianTailBoxUpper_stage_twenty_three_point_sum :
    gaussianTailBoxUpper 2 20 + gaussianTailBoxUpper 3 20 +
        gaussianTailBoxUpper 4 20 <= 61 / 144 := by
  have h := gaussianTailBoxUpper_stage_twenty_ladder
  grind

theorem gaussianTailBoxUpper_stage_twenty_four_point_sum :
    gaussianTailBoxUpper 2 20 + gaussianTailBoxUpper 3 20 +
        gaussianTailBoxUpper 4 20 + gaussianTailBoxUpper 5 20 <=
      1669 / 3600 := by
  have h := gaussianTailBoxUpper_stage_twenty_ladder_four
  grind

theorem gaussianTailBoxUpper_stage_twenty_eight_point_sum :
    gaussianTailBoxUpper 2 20 + gaussianTailBoxUpper 3 20 +
        gaussianTailBoxUpper 4 20 + gaussianTailBoxUpper 5 20 +
        gaussianTailBoxUpper 6 100 + gaussianTailBoxUpper 7 100 +
        gaussianTailBoxUpper 8 100 <= 3349341 / 6350400 := by
  have h := gaussianTailBoxUpper_stage_twenty_ladder_eight
  grind

end ComputableAnalysis
