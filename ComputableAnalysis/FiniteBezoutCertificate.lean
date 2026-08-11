import ComputableAnalysis.Basic

namespace ComputableAnalysis

/-! A concrete terminating Euclidean/Bézout certificate for item 60. -/

theorem euclideanGcd_84_30 :
    euclideanGcd 84 30 = 6 := by
  native_decide

theorem bezout_84_30 :
    (-1 : Int) * 84 + 3 * 30 = (euclideanGcd 84 30 : Int) := by
  rw [euclideanGcd_84_30]
  native_decide

theorem bezout_84_30_certificate :
    euclideanGcd 84 30 = 6 /\
      (-1 : Int) * 84 + 3 * 30 = 6 := by
  constructor
  · exact euclideanGcd_84_30
  · have h := bezout_84_30
    rw [euclideanGcd_84_30] at h
    exact h

end ComputableAnalysis
