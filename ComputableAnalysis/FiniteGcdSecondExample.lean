import ComputableAnalysis.Basic

/-!
# A second Euclidean/Bézout certificate

The terminating rational-project arithmetic loop is evaluated on `(252,198)`
and paired with its explicit integer back-substitution coefficients.
-/

namespace ComputableAnalysis

theorem euclideanGcd_252_198 :
    euclideanGcd 252 198 = 18 := by
  native_decide

theorem bezout_252_198 :
    (4 : Int) * 252 + (-5) * 198 = (euclideanGcd 252 198 : Int) := by
  rw [euclideanGcd_252_198]
  native_decide

theorem bezout_252_198_certificate :
    euclideanGcd 252 198 = 18 ∧
      (4 : Int) * 252 + (-5) * 198 = 18 := by
  constructor
  · exact euclideanGcd_252_198
  · have h := bezout_252_198
    rw [euclideanGcd_252_198] at h
    exact h

theorem euclideanGcd_1071_462 :
    euclideanGcd 1071 462 = 21 := by
  native_decide

theorem bezout_1071_462 :
    (-3 : Int) * 1071 + 7 * 462 = (euclideanGcd 1071 462 : Int) := by
  rw [euclideanGcd_1071_462]
  native_decide

theorem bezout_1071_462_certificate :
    euclideanGcd 1071 462 = 21 /\
      (-3 : Int) * 1071 + 7 * 462 = 21 := by
  constructor
  · exact euclideanGcd_1071_462
  · have h := bezout_1071_462
    rw [euclideanGcd_1071_462] at h
    exact h

theorem euclideanGcd_12345_6789 :
    euclideanGcd 12345 6789 = 3 := by
  native_decide

theorem bezout_12345_6789 :
    (-903 : Int) * 12345 + 1642 * 6789 =
      (euclideanGcd 12345 6789 : Int) := by
  rw [euclideanGcd_12345_6789]
  native_decide

theorem bezout_12345_6789_certificate :
    euclideanGcd 12345 6789 = 3 /\
      (-903 : Int) * 12345 + 1642 * 6789 = 3 := by
  constructor
  · exact euclideanGcd_12345_6789
  · have h := bezout_12345_6789
    rw [euclideanGcd_12345_6789] at h
    exact h

end ComputableAnalysis
