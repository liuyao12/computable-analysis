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

end ComputableAnalysis
