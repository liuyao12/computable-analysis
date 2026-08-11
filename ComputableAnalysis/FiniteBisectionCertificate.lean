import ComputableAnalysis.FiniteBisectionIteration

namespace ComputableAnalysis

/-! A concrete finite bisection trace for the affine root `x = 1/2`.
The interval is retained as rational data at every stage; no zero-existence
or completeness theorem is used.
-/

def affineHalf : Rat -> Rat := fun x => x - 1 / 2

def affineHalfInitial : QInterval := { lo := 0, hi := 1 }

theorem affineHalf_bisection_stage3 :
    monotoneBisectionIterate affineHalf 3 affineHalfInitial =
      { lo := 3 / 8, hi := 1 / 2 } := by
  native_decide

theorem affineHalf_bisection_stage3_bracket :
    affineHalf (monotoneBisectionIterate affineHalf 3 affineHalfInitial).lo <= 0 /\
      0 <= affineHalf
        (monotoneBisectionIterate affineHalf 3 affineHalfInitial).hi := by
  rw [affineHalf_bisection_stage3]
  native_decide

theorem affineHalf_bisection_stage3_width :
    (monotoneBisectionIterate affineHalf 3 affineHalfInitial).width = 1 / 8 := by
  rw [affineHalf_bisection_stage3]
  native_decide

end ComputableAnalysis
