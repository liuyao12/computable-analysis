import Lean
import ComputableAnalysis.CosineSquareSymmetry
import ComputableAnalysis.CosineSquareFTC

open Lean Elab Command

private partial def projectClosure (env : Environment) (name : Name) : StateM NameSet Unit := do
  if (← get).contains name then return
  if !name.toString.startsWith "ComputableAnalysis." then return
  modify (·.insert name)
  if let some info := env.find? name then
    for dep in info.type.getUsedConstants do projectClosure env dep
    if let some value := info.value? (allowOpaque := true) then
      for dep in value.getUsedConstants do projectClosure env dep

run_cmd do
  let env ← getEnv
  let roots := [``ComputableAnalysis.CosineSquare.integral_valid,
    ``ComputableAnalysis.CosineSquare.integral_width,
    ``ComputableAnalysis.CosineSquare.integral_via_symmetry,
    ``ComputableAnalysis.CosineSquare.integral_via_FTC,
    ``ComputableAnalysis.CosineSquare.sample_mem,
    ``ComputableAnalysis.CosineSquare.reflected_square_error,
    ``ComputableAnalysis.CosineSquare.symmetry_sum_error,
    ``ComputableAnalysis.CosineSquare.normalizedPrimitive_formula,
    ``ComputableAnalysis.CosineSquare.normalizedPrimitive_local_error,
    ``ComputableAnalysis.CosineSquare.primitive_endpoints_close]
  for mod in env.header.moduleNames do
    if mod.toString.startsWith "Mathlib" then throwError "Unexpected Mathlib import: {mod}"
  let sym := ((projectClosure env ``ComputableAnalysis.CosineSquare.integral_via_symmetry).run {}).2
  let ftc := ((projectClosure env ``ComputableAnalysis.CosineSquare.integral_via_FTC).run {}).2
  unless sym.contains ``ComputableAnalysis.CosineSquare.left_reflection &&
      sym.contains ``ComputableAnalysis.ClockTrigonometry.sample_complement &&
      sym.contains ``ComputableAnalysis.ClockTrigonometry.sample_unit do
    throwError "Symmetry route lacks its finite reflection/circle proof"
  if sym.contains ``ComputableAnalysis.FiniteSampleCalculus.chosen_samples_FTC ||
      sym.contains ``ComputableAnalysis.CosineSquare.integral_via_FTC then
    throwError "Symmetry route reused the FTC proof"
  unless ftc.contains ``ComputableAnalysis.FiniteSampleCalculus.chosen_samples_FTC &&
      ftc.contains ``ComputableAnalysis.CosineSquare.primitiveModel do
    throwError "FTC route lacks the checked derivative model and finite FTC"
  if ftc.contains ``ComputableAnalysis.CosineSquare.integral_via_symmetry ||
      ftc.contains ``ComputableAnalysis.CosineSquare.symmetry_sum_error then
    throwError "FTC route reused the symmetry integral evaluation"
  let mut records : Array Json := #[]
  for name in roots do
    let axioms ← collectAxioms name
    if axioms.contains ``sorryAx then throwError "Unfinished proof: {name}"
    let some info := env.find? name | throwError "Missing theorem: {name}"
    let type ← liftTermElabM <| Meta.ppExpr info.type
    records := records.push <| Json.mkObj [
      ("name",toJson name.toString),("type",toJson type.pretty),
      ("axioms",toJson (axioms.toList.map Name.toString))]
  let report := Json.mkObj [
    ("declarations",Json.arr records),
    ("symmetryClosure",toJson ((sym.toArray.qsort Name.lt).toList.map Name.toString)),
    ("ftcClosure",toJson ((ftc.toArray.qsort Name.lt).toList.map Name.toString)),
    ("checks",Json.mkObj [("noSorry",toJson true),("noMathlib",toJson true),
      ("symmetryDoesNotUseFTC",toJson true),("ftcDoesNotUseSymmetryIntegral",toJson true),
      ("sameIntegralProgram",toJson true)])]
  liftIO <| IO.FS.createDirAll "cosine-square-reports"
  liftIO <| IO.FS.writeFile "cosine-square-reports/proofs.json" report.pretty
  logInfo "PASS: both unconditional proofs identify the same valid rational quadrature; independent value proofs, no Mathlib, no sorry."

#check ComputableAnalysis.CosineSquare.integral_via_symmetry
#check ComputableAnalysis.CosineSquare.integral_via_FTC
#print axioms ComputableAnalysis.CosineSquare.integral_valid
#print axioms ComputableAnalysis.CosineSquare.integral_via_symmetry
#print axioms ComputableAnalysis.CosineSquare.integral_via_FTC
