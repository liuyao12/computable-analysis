import Lean
import ComputableAnalysis.CosineSquareSymmetry
import ComputableAnalysis.CosineSquareFTC
import ComputableAnalysis.TrigSquareGlobal

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
    ``ComputableAnalysis.CosineSquare.primitive_endpoints_close,
    ``ComputableAnalysis.TrigSquareGlobal.cosineIntegral_valid,
    ``ComputableAnalysis.TrigSquareGlobal.sineIntegral_valid,
    ``ComputableAnalysis.TrigSquareGlobal.cosineClosedForm_valid,
    ``ComputableAnalysis.TrigSquareGlobal.sineClosedForm_valid,
    ``ComputableAnalysis.TrigSquareGlobal.cosine_definite_integral,
    ``ComputableAnalysis.TrigSquareGlobal.sine_definite_integral,
    ``ComputableAnalysis.TrigSquareGlobal.cosine_definite_integral_via_Euler,
    ``ComputableAnalysis.TrigSquareGlobal.sine_definite_integral_via_Euler,
    ``ComputableAnalysis.TrigSquareGlobal.cosine_representation_equiv,
    ``ComputableAnalysis.TrigSquareGlobal.sine_representation_equiv,
    ``ComputableAnalysis.TrigSquareGlobal.cosine_half_integer,
    ``ComputableAnalysis.TrigSquareGlobal.sine_half_integer,
    ``ComputableAnalysis.TrigSquareGlobal.closed_form_sample,
    ``ComputableAnalysis.TrigSquareGlobal.cell_quadrature,
    ``ComputableAnalysis.TrigSquareGlobal.whole_cell_agreement,
    ``ComputableAnalysis.TrigSquareVariable.definite_integral,
    ``ComputableAnalysis.TrigSquareVariable.definite_integral_via_Euler,
    ``ComputableAnalysis.TrigSquareVariable.sineSumSample_mem,
    ``ComputableAnalysis.TrigSquareEuler.euler_characterization,
    ``ComputableAnalysis.TrigSquareEuler.cosine_integral_via_Euler,
    ``ComputableAnalysis.TrigSquareEuler.sine_integral_via_Euler,
    ``ComputableAnalysis.ImaginaryExponentialIntegral.real_integral_equiv,
    ``ComputableAnalysis.ImaginaryExponentialIntegral.integrate_imag,
    ``ComputableAnalysis.ImaginaryExponentialIntegral.solution_unique,
    ``ComputableAnalysis.RationalLipschitzLift.Data.at_rational,
    ``ComputableAnalysis.RationalLipschitzLift.Data.representation_equiv,
    ``ComputableAnalysis.RationalLipschitzLift.Data.congr]
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
  let euler := ((projectClosure env ``ComputableAnalysis.TrigSquareVariable.definite_integral_via_Euler).run {}).2
  unless euler.contains ``ComputableAnalysis.ImaginaryExponentialIntegral.realEndpointModel &&
      euler.contains ``ComputableAnalysis.FiniteSampleCalculus.chosen_samples_FTC do
    throwError "Euler route lacks exponential integration and quadrature comparison"
  for forbidden in [``ComputableAnalysis.CosineSquare.primitiveModel,
      ``ComputableAnalysis.TrigSquareVariable.sum_FTC,
      ``ComputableAnalysis.TrigSquareVariable.definite_integral,
      ``ComputableAnalysis.CosineSquare.integral_via_FTC,
      ``ComputableAnalysis.CosineSquare.integral_via_symmetry] do
    if euler.contains forbidden then throwError "Euler local value proof reused {forbidden}"
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
    ("eulerLocalClosure",toJson ((euler.toArray.qsort Name.lt).toList.map Name.toString)),
    ("ftcClosure",toJson ((ftc.toArray.qsort Name.lt).toList.map Name.toString)),
    ("checks",Json.mkObj [("noSorry",toJson true),("noMathlib",toJson true),
      ("symmetryDoesNotUseFTC",toJson true),("ftcDoesNotUseSymmetryIntegral",toJson true),
      ("sameIntegralProgram",toJson true),("eulerLocalValueProofIndependent",toJson true),
      ("arbitraryRepresentedEndpoints",toJson true),("halfIntegerCorollaries",toJson true)])]
  liftIO <| IO.FS.createDirAll "cosine-square-reports"
  liftIO <| IO.FS.writeFile "cosine-square-reports/proofs.json" report.pretty
  logInfo "PASS: arbitrary represented endpoints, sine/cosine square formulas, Euler integration, representation invariance and half-integer corollaries; no Mathlib, no sorry."

#check ComputableAnalysis.CosineSquare.integral_via_symmetry
#check ComputableAnalysis.CosineSquare.integral_via_FTC
#print axioms ComputableAnalysis.CosineSquare.integral_valid
#print axioms ComputableAnalysis.CosineSquare.integral_via_symmetry
#print axioms ComputableAnalysis.CosineSquare.integral_via_FTC
