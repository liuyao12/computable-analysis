import ComputableAnalysis.IntegralApplications
import Lean

/-! Actual executions of the new native definitions, not a Python substitute.
The published decimal rendering is rounded outwards from these exact rationals. -/
open Lean ComputableAnalysis
#eval do
  let mut products : Array Json := #[]
  for n in [0,1,4,16,64] do
    let lo := 2*Wallis.product n
    let hi := 2*(Wallis.coefficient (2*n+1)/Wallis.coefficient (2*n+2))
    unless lo ≤ hi do throw <| IO.userError "Invalid Wallis interval"
    products := products.push <| Json.mkObj [
      ("n",toJson n),("lower",toJson (toString lo)),("upper",toJson (toString hi))]
  let mut betas : Array Json := #[]
  for (m,n) in [(0,0),(1,1),(2,3),(4,5)] do
    let stage := 5
    let box := (BetaIntegral.integral m n).compute stage
    let exact := BetaIntegral.value m n
    unless box.lo ≤ exact && exact ≤ box.hi do throw <| IO.userError "Beta check failed"
    betas := betas.push <| Json.mkObj [
      ("m",toJson m),("n",toJson n),("stage",toJson stage),
      ("lower",toJson (toString box.lo)),("upper",toJson (toString box.hi)),
      ("rationalValue",toJson (toString exact))]
  IO.FS.createDirAll "comparison/reports"
  IO.FS.writeFile "comparison/reports/integral-native-examples.json"
    ((Json.mkObj [("wallisBounds",toJson products),("betaOutputs",toJson betas),
      ("execution",toJson "Compiled Lean definitions; exact rational outputs, no Mathlib or Python evaluator.")]).compress ++ "\n")
  IO.println "PASS: compiled Lean Wallis products and beta quadrature samples"
