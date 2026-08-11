import ComputableAnalysis.FiniteSquareRootBisectionExample

/-!
# A finite fourth-root bisection trace

The target `2` is bracketed under the monotone rational map `x ↦ x^4` on
`[1,2]`.  The trace is finite rational data; it does not treat the fourth
root as an attained completed-real point.
-/

namespace ComputableAnalysis

def fourthTarget : Rat -> Rat := fun x => x ^ 4

def fourthTargetInitial : QInterval := { lo := 1, hi := 2 }

theorem fourthTarget_bisection_stage8 :
    monotoneTargetBisectionIterate fourthTarget 2 8 fourthTargetInitial =
      { lo := 19 / 16, hi := 305 / 256 } := by
  native_decide

theorem fourthTarget_bisection_stage8_bracket :
    fourthTarget
        (monotoneTargetBisectionIterate fourthTarget 2 8
          fourthTargetInitial).lo <= 2 /\
      2 <= fourthTarget
        (monotoneTargetBisectionIterate fourthTarget 2 8
          fourthTargetInitial).hi := by
  rw [fourthTarget_bisection_stage8]
  native_decide

theorem fourthTarget_bisection_stage8_width :
    (monotoneTargetBisectionIterate fourthTarget 2 8
      fourthTargetInitial).width = 1 / 256 := by
  rw [fourthTarget_bisection_stage8]
  native_decide

theorem fourthTarget_bisection_stage16 :
    monotoneTargetBisectionIterate fourthTarget 2 16 fourthTargetInitial =
      { lo := 77935 / 65536, hi := 4871 / 4096 } := by
  native_decide

theorem fourthTarget_bisection_stage16_bracket :
    fourthTarget
        (monotoneTargetBisectionIterate fourthTarget 2 16
          fourthTargetInitial).lo <= 2 /\
      2 <= fourthTarget
        (monotoneTargetBisectionIterate fourthTarget 2 16
          fourthTargetInitial).hi := by
  rw [fourthTarget_bisection_stage16]
  native_decide

theorem fourthTarget_bisection_stage16_width :
    (monotoneTargetBisectionIterate fourthTarget 2 16
      fourthTargetInitial).width = 1 / 65536 := by
  rw [fourthTarget_bisection_stage16]
  native_decide

theorem fourthTarget_bisection_stage24 :
    monotoneTargetBisectionIterate fourthTarget 2 24 fourthTargetInitial =
      { lo := 623487 / 524288, hi := 19951585 / 16777216 } := by
  native_decide

theorem fourthTarget_bisection_stage24_bracket :
    fourthTarget
        (monotoneTargetBisectionIterate fourthTarget 2 24
          fourthTargetInitial).lo <= 2 /\
      2 <= fourthTarget
        (monotoneTargetBisectionIterate fourthTarget 2 24
          fourthTargetInitial).hi := by
  rw [fourthTarget_bisection_stage24]
  native_decide

theorem fourthTarget_bisection_stage24_width :
    (monotoneTargetBisectionIterate fourthTarget 2 24
      fourthTargetInitial).width = 1 / 16777216 := by
  rw [fourthTarget_bisection_stage24]
  native_decide

end ComputableAnalysis
