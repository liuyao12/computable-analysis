import ComputableAnalysis.FiniteBisectionIteration

/-!
# A finite bisection trace for `sqrt 2`

This is a concrete rational certificate for the equation `x^2 = 2` on `[1,2]`.
The value `sqrt 2` is never treated as an attained endpoint: each stage is a
finite comparison producing a narrower rational enclosure.
-/

namespace ComputableAnalysis

def sqrtTwoTarget : Rat -> Rat := fun x => x ^ 2

def sqrtTwoInitial : QInterval := { lo := 1, hi := 2 }

theorem sqrtTwo_bisection_stage4 :
    monotoneTargetBisectionIterate sqrtTwoTarget 2 4 sqrtTwoInitial =
      { lo := 11 / 8, hi := 23 / 16 } := by
  native_decide

theorem sqrtTwo_bisection_stage4_bracket :
    sqrtTwoTarget
        (monotoneTargetBisectionIterate sqrtTwoTarget 2 4
          sqrtTwoInitial).lo <= 2 /\
      2 <= sqrtTwoTarget
        (monotoneTargetBisectionIterate sqrtTwoTarget 2 4
          sqrtTwoInitial).hi := by
  rw [sqrtTwo_bisection_stage4]
  native_decide

theorem sqrtTwo_bisection_stage4_width :
    (monotoneTargetBisectionIterate sqrtTwoTarget 2 4
      sqrtTwoInitial).width = 1 / 16 := by
  rw [sqrtTwo_bisection_stage4]
  native_decide

theorem sqrtTwo_bisection_stage8 :
    monotoneTargetBisectionIterate sqrtTwoTarget 2 8 sqrtTwoInitial =
      { lo := 181 / 128, hi := 363 / 256 } := by
  native_decide

theorem sqrtTwo_bisection_stage8_bracket :
    sqrtTwoTarget
        (monotoneTargetBisectionIterate sqrtTwoTarget 2 8
          sqrtTwoInitial).lo <= 2 /\
      2 <= sqrtTwoTarget
        (monotoneTargetBisectionIterate sqrtTwoTarget 2 8
          sqrtTwoInitial).hi := by
  rw [sqrtTwo_bisection_stage8]
  native_decide

theorem sqrtTwo_bisection_stage8_width :
    (monotoneTargetBisectionIterate sqrtTwoTarget 2 8
      sqrtTwoInitial).width = 1 / 256 := by
  rw [sqrtTwo_bisection_stage8]
  native_decide

theorem sqrtTwo_bisection_stage12 :
    monotoneTargetBisectionIterate sqrtTwoTarget 2 12 sqrtTwoInitial =
      { lo := 181 / 128, hi := 5793 / 4096 } := by
  native_decide

theorem sqrtTwo_bisection_stage12_bracket :
    sqrtTwoTarget
        (monotoneTargetBisectionIterate sqrtTwoTarget 2 12
          sqrtTwoInitial).lo <= 2 /\
      2 <= sqrtTwoTarget
        (monotoneTargetBisectionIterate sqrtTwoTarget 2 12
          sqrtTwoInitial).hi := by
  rw [sqrtTwo_bisection_stage12]
  native_decide

theorem sqrtTwo_bisection_stage12_width :
    (monotoneTargetBisectionIterate sqrtTwoTarget 2 12
      sqrtTwoInitial).width = 1 / 4096 := by
  rw [sqrtTwo_bisection_stage12]
  native_decide

theorem sqrtTwo_bisection_stage16 :
    monotoneTargetBisectionIterate sqrtTwoTarget 2 16 sqrtTwoInitial =
      { lo := 92681 / 65536, hi := 46341 / 32768 } := by
  native_decide

theorem sqrtTwo_bisection_stage16_bracket :
    sqrtTwoTarget
        (monotoneTargetBisectionIterate sqrtTwoTarget 2 16
          sqrtTwoInitial).lo <= 2 /\
      2 <= sqrtTwoTarget
        (monotoneTargetBisectionIterate sqrtTwoTarget 2 16
          sqrtTwoInitial).hi := by
  rw [sqrtTwo_bisection_stage16]
  native_decide

theorem sqrtTwo_bisection_stage16_width :
    (monotoneTargetBisectionIterate sqrtTwoTarget 2 16
      sqrtTwoInitial).width = 1 / 65536 := by
  rw [sqrtTwo_bisection_stage16]
  native_decide

theorem sqrtTwo_bisection_stage20 :
    monotoneTargetBisectionIterate sqrtTwoTarget 2 20 sqrtTwoInitial =
      { lo := 741455 / 524288, hi := 1482911 / 1048576 } := by
  native_decide

theorem sqrtTwo_bisection_stage20_bracket :
    sqrtTwoTarget
        (monotoneTargetBisectionIterate sqrtTwoTarget 2 20
          sqrtTwoInitial).lo <= 2 /\
      2 <= sqrtTwoTarget
        (monotoneTargetBisectionIterate sqrtTwoTarget 2 20
          sqrtTwoInitial).hi := by
  rw [sqrtTwo_bisection_stage20]
  native_decide

theorem sqrtTwo_bisection_stage20_width :
    (monotoneTargetBisectionIterate sqrtTwoTarget 2 20
      sqrtTwoInitial).width = 1 / 1048576 := by
  rw [sqrtTwo_bisection_stage20]
  native_decide

theorem sqrtTwo_bisection_stage24 :
    monotoneTargetBisectionIterate sqrtTwoTarget 2 24 sqrtTwoInitial =
      { lo := 11863283 / 8388608, hi := 23726567 / 16777216 } := by
  native_decide

theorem sqrtTwo_bisection_stage24_bracket :
    sqrtTwoTarget
        (monotoneTargetBisectionIterate sqrtTwoTarget 2 24
          sqrtTwoInitial).lo <= 2 /\
      2 <= sqrtTwoTarget
        (monotoneTargetBisectionIterate sqrtTwoTarget 2 24
          sqrtTwoInitial).hi := by
  rw [sqrtTwo_bisection_stage24]
  native_decide

theorem sqrtTwo_bisection_stage24_width :
    (monotoneTargetBisectionIterate sqrtTwoTarget 2 24
      sqrtTwoInitial).width = 1 / 16777216 := by
  rw [sqrtTwo_bisection_stage24]
  native_decide

end ComputableAnalysis
