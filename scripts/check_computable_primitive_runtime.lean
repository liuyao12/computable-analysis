import ComputableAnalysis.ComputablePrimitiveDerivativeExamples

/-! Runtime smoke check: termination proofs must erase to executable rational
width searches, and the concrete irrational primitive boxes must narrow. -/
open ComputableAnalysis ComputableCoefficient ComputableLogarithmChart
open ComputablePrimitiveDerivativeExamples

#eval do
  let eps : QPos := ⟨1/16, by decide +kernel⟩
  let stage := widthStage ComputablePrimitiveExamples.rootTwo eps
  unless (ComputablePrimitiveExamples.rootTwo.compute stage).width ≤ eps.val do
    throw (IO.userError "coefficient accuracy search failed")
  for (name, raw) in [
      ("irrational pole", rawCoordinate false ((simplePoleChart inverse).value (1/16))),
      ("irrational arctangent", rawCoordinate true ((arctanChart pole).value (1/16))),
      ("irrational quadratic", rawCoordinate true (quadraticAtanChart.weightedValue (1/16)))] do
    let coarse := raw.compute 0
    let fine := raw.compute 4
    unless coarse.lo ≤ fine.lo && fine.lo ≤ fine.hi && fine.hi ≤ coarse.hi do
      throw (IO.userError (name ++ ": invalid nesting"))
    unless fine.width < coarse.width do
      throw (IO.userError (name ++ ": boxes failed to narrow"))
    IO.println ("PASS: " ++ name ++ " executable nested narrowing boxes")
