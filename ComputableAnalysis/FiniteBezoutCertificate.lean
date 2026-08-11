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

theorem euclideanGcd_99991_12345 :
    euclideanGcd 99991 12345 = 1 := by
  native_decide

theorem bezout_99991_12345 :
    (2116 : Int) * 99991 + (-17139) * 12345 =
      (euclideanGcd 99991 12345 : Int) := by
  rw [euclideanGcd_99991_12345]
  native_decide

theorem bezout_99991_12345_certificate :
    euclideanGcd 99991 12345 = 1 /\
      (2116 : Int) * 99991 + (-17139) * 12345 = 1 := by
  constructor
  · exact euclideanGcd_99991_12345
  · have h := bezout_99991_12345
    rw [euclideanGcd_99991_12345] at h
    exact h

end ComputableAnalysis
