import ComputableAnalysis.FiniteBisectionIteration

/-!
# A finite square-root bisection trace

The target `1/2` is bracketed under the monotone rational map `x ↦ x^2` on
`[0,1]`.  The endpoint is not treated as an attained irrational value: each
stage is an explicit rational interval selected by a finite comparison.
-/

namespace ComputableAnalysis

def squareTarget : Rat -> Rat := fun x => x ^ 2

def squareTargetInitial : QInterval := { lo := 0, hi := 1 }

theorem squareTarget_bisection_stage4 :
    monotoneTargetBisectionIterate squareTarget (1 / 2) 4
        squareTargetInitial =
      { lo := 11 / 16, hi := 3 / 4 } := by
  native_decide

theorem squareTarget_bisection_stage4_bracket :
    squareTarget
        (monotoneTargetBisectionIterate squareTarget (1 / 2) 4
          squareTargetInitial).lo <= 1 / 2 /\
      1 / 2 <= squareTarget
        (monotoneTargetBisectionIterate squareTarget (1 / 2) 4
          squareTargetInitial).hi := by
  rw [squareTarget_bisection_stage4]
  native_decide

theorem squareTarget_bisection_stage4_width :
    (monotoneTargetBisectionIterate squareTarget (1 / 2) 4
      squareTargetInitial).width = 1 / 16 := by
  rw [squareTarget_bisection_stage4]
  native_decide

end ComputableAnalysis
