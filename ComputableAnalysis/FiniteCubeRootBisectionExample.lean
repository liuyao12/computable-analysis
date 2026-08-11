import ComputableAnalysis.FiniteSquareRootBisectionExample

/-!
# A finite cube-root bisection trace

The target `2` is bracketed under the monotone rational map `x ↦ x^3` on
`[1,2]`.  Every endpoint and comparison is rational data; the example does
not treat the cube root as an attained completed-real point.
-/

namespace ComputableAnalysis

def cubeTarget : Rat -> Rat := fun x => x ^ 3

def cubeTargetInitial : QInterval := { lo := 1, hi := 2 }

theorem cubeTarget_bisection_stage4 :
    monotoneTargetBisectionIterate cubeTarget 2 4 cubeTargetInitial =
      { lo := 5 / 4, hi := 21 / 16 } := by
  native_decide

theorem cubeTarget_bisection_stage4_bracket :
    cubeTarget
        (monotoneTargetBisectionIterate cubeTarget 2 4 cubeTargetInitial).lo
        <= 2 /\
      2 <= cubeTarget
        (monotoneTargetBisectionIterate cubeTarget 2 4 cubeTargetInitial).hi := by
  rw [cubeTarget_bisection_stage4]
  native_decide

theorem cubeTarget_bisection_stage4_width :
    (monotoneTargetBisectionIterate cubeTarget 2 4 cubeTargetInitial).width =
      1 / 16 := by
  rw [cubeTarget_bisection_stage4]
  native_decide

theorem cubeTarget_bisection_stage8 :
    monotoneTargetBisectionIterate cubeTarget 2 8 cubeTargetInitial =
      { lo := 161 / 128, hi := 323 / 256 } := by
  native_decide

theorem cubeTarget_bisection_stage8_bracket :
    cubeTarget
        (monotoneTargetBisectionIterate cubeTarget 2 8 cubeTargetInitial).lo
        <= 2 /\
      2 <= cubeTarget
        (monotoneTargetBisectionIterate cubeTarget 2 8 cubeTargetInitial).hi := by
  rw [cubeTarget_bisection_stage8]
  native_decide

theorem cubeTarget_bisection_stage8_width :
    (monotoneTargetBisectionIterate cubeTarget 2 8 cubeTargetInitial).width =
      1 / 256 := by
  rw [cubeTarget_bisection_stage8]
  native_decide

theorem cubeTarget_bisection_stage16 :
    monotoneTargetBisectionIterate cubeTarget 2 16 cubeTargetInitial =
      { lo := 41285 / 32768, hi := 82571 / 65536 } := by
  native_decide

theorem cubeTarget_bisection_stage16_bracket :
    cubeTarget
        (monotoneTargetBisectionIterate cubeTarget 2 16 cubeTargetInitial).lo
        <= 2 /\
      2 <= cubeTarget
        (monotoneTargetBisectionIterate cubeTarget 2 16 cubeTargetInitial).hi := by
  rw [cubeTarget_bisection_stage16]
  native_decide

theorem cubeTarget_bisection_stage16_width :
    (monotoneTargetBisectionIterate cubeTarget 2 16 cubeTargetInitial).width =
      1 / 65536 := by
  rw [cubeTarget_bisection_stage16]
  native_decide

theorem cubeTarget_bisection_stage24 :
    monotoneTargetBisectionIterate cubeTarget 2 24 cubeTargetInitial =
      { lo := 21137967 / 16777216, hi := 1321123 / 1048576 } := by
  native_decide

theorem cubeTarget_bisection_stage24_bracket :
    cubeTarget
        (monotoneTargetBisectionIterate cubeTarget 2 24 cubeTargetInitial).lo
        <= 2 /\
      2 <= cubeTarget
        (monotoneTargetBisectionIterate cubeTarget 2 24 cubeTargetInitial).hi := by
  rw [cubeTarget_bisection_stage24]
  native_decide

theorem cubeTarget_bisection_stage24_width :
    (monotoneTargetBisectionIterate cubeTarget 2 24 cubeTargetInitial).width =
      1 / 16777216 := by
  rw [cubeTarget_bisection_stage24]
  native_decide

end ComputableAnalysis
