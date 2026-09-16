import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Lean

/-! Exact checked statements for the reader's Mathlib integration branch.
This file exports documentation; no production proof imports it. -/
namespace MathlibMapExport
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def selected : Array Name := #[
  ``MeasureTheory.SimpleFunc.lintegral,
  ``MeasureTheory.lintegral,
  ``MeasureTheory.lintegral_def,
  ``MeasureTheory.HasFiniteIntegral,
  ``MeasureTheory.Integrable,
  ``MeasureTheory.SimpleFunc.integral,
  ``MeasureTheory.L1.integralCLM,
  ``MeasureTheory.L1.integral,
  ``MeasureTheory.L1.integral_def,
  ``MeasureTheory.L1.setToL1,
  ``MeasureTheory.setToFun,
  ``MeasureTheory.integral,
  ``MeasureTheory.integral_def,
  ``MeasureTheory.integral_eq_setToFun,
  ``intervalIntegral,
  ``IntervalIntegrable,
  ``MeasureTheory.Measure.restrict,
  ``intervalIntegral.integral_of_le,
  ``intervalIntegral.integral_mono_on,
  ``intervalIntegral.integral_add_adjacent_intervals,
  ``intervalIntegral.integral_eq_sub_of_hasDerivAt,
  ``intervalIntegral.integral_deriv_eq_sub,
  ``intervalIntegral.integral_deriv_eq_sub',
  ``Real.hasDerivAt_sin,
  ``Real.deriv_sin,
  ``integral_cos]

def showBody : Array Name := #[
  ``MeasureTheory.SimpleFunc.lintegral, ``MeasureTheory.HasFiniteIntegral,
  ``MeasureTheory.Integrable, ``intervalIntegral, ``IntervalIntegrable]

run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for name in selected do
    let some ci := env.find? name | throwError "Missing Mathlib declaration {name}"
    let axioms ← collectAxioms name
    if axioms.contains `sorryAx then throwError "Admitted declaration {name}"
    let owner := match env.getModuleIdxFor? name with
      | some i => env.header.moduleNames[i.toNat]!.toString
      | none => ""
    unless owner.startsWith "Mathlib." do throwError "Unexpected owner {name}: {owner}"
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def"
      | .inductInfo _ => "inductive" | _ => "constant"
    let type ← liftTermElabM do return (← Meta.ppExpr ci.type).pretty 92
    let value ← if showBody.contains name then
      match ci.value? true with
      | some v => liftTermElabM do return Json.str ((← Meta.ppExpr v).pretty 92)
      | none => pure Json.null
      else pure Json.null
    let range ← findDeclarationRanges? name
    let source := match range with
      | none => Json.null
      | some r => Json.mkObj [("start",toJson r.range.pos.line),("end",toJson r.range.endPos.line)]
    rows := rows.push <| Json.mkObj [
      ("name",toJson name.toString),("kind",toJson kind),("type",toJson type),
      ("value",value),("ownerModule",toJson owner),("sourceRange",source),
      ("noncomputable",toJson (isNoncomputable env name)),
      ("typeRefs",toJson (ci.type.getUsedConstants.map Name.toString)),
      ("bodyRefs",toJson ((((ci.value? true).map Expr.getUsedConstants).getD #[]).map Name.toString))]
  IO.FS.createDirAll "reports"
  IO.FS.writeFile "reports/mathlib-map-statements.json" ((Json.mkObj [
    ("leanVersion",toJson Lean.versionString),("declarations",toJson rows),
    ("checks",Json.mkObj [("exportedFromLean",toJson true),("noSorryAx",toJson true)])]).compress ++ "\n")
  logInfo m!"PASS: exported {rows.size} Mathlib integral/FTC declarations from the checked environment"
end MathlibMapExport
