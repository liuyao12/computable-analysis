import ComputableAnalysis.IntegralSchedules
import ComputableAnalysis.CosinePrimitive
import MathlibComparison.CosinePrimitive
import Lean

/-! Reader metadata only. No original theorem imports this exporter. -/
namespace ScheduleMapExport
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def selected : Array Name := #[
  ``ComputableAnalysis.Integral.ScheduledBounds.JointSchedule,
  ``ComputableAnalysis.Integral.ScheduledBounds.JointSchedule.meshStage,
  ``ComputableAnalysis.Integral.ScheduledBounds.JointSchedule.evaluationStage,
  ``ComputableAnalysis.Integral.ScheduledBounds.selected,
  ``ComputableAnalysis.Integral.ScheduledBounds.raw,
  ``ComputableAnalysis.Integral.ScheduledBounds.Certificate,
  ``ComputableAnalysis.Integral.ScheduledBounds.Certificate.compatible,
  ``ComputableAnalysis.Integral.ScheduledBounds.Certificate.shrinking,
  ``ComputableAnalysis.Integral.ScheduledBounds.valid,
  ``ComputableAnalysis.Integral.ScheduledBounds.equivalent,
  ``ComputableAnalysis.Integral.Dovetail.raw,
  ``ComputableAnalysis.Integral.Dovetail.raw_valid,
  ``ComputableAnalysis.Integral.Dovetail.ofBoxes_valid,
  ``ComputableAnalysis.CosineFTC.fixedMesh_valid,
  ``ComputableAnalysis.CosineFTC.error_shrinks,
  ``ComputableAnalysis.CosinePrimitive.S_zero,
  ``ComputableAnalysis.CosinePrimitive.endpoints_from_zero,
  ``ComputableAnalysis.CosinePrimitive.integral_valid_viaInequalities,
  ``ComputableAnalysis.CosinePrimitive.integral_valid_viaFTC,
  ``ComputableAnalysis.CosinePrimitive.integral_valid_viaMathlib,
  ``MathlibComparison.primitive_endpoint_represents,
  ``MathlibComparison.primitive_integral_represents,
  ``MathlibComparison.equiv_of_represents]

def refs (ci : ConstantInfo) : Array Name := ci.type.getUsedConstants ++
  ((ci.value? true).map Expr.getUsedConstants).getD #[]

partial def closure (env : Environment) (todo : List Name) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env rest seen else
      let next := match env.find? n with | none => [] | some ci => (refs ci).toList
      closure env (next ++ rest) (seen.insert n)

run_cmd do
  let env ← getEnv
  for root in [``ComputableAnalysis.Integral.ScheduledBounds.valid,
      ``ComputableAnalysis.Integral.ScheduledBounds.equivalent] do
    let axs ← collectAxioms root
    if axs.contains `sorryAx then throwError "Admitted schedule lemma: {root}"
    for n in closure env [root] do
      if let some i := env.getModuleIdxFor? n then
        let m := env.header.moduleNames[i.toNat]!.toString
        if m.startsWith "Mathlib" then throwError "Schedule theorem imports Mathlib: {n}"
        if m.startsWith "ComputableAnalysis" && isNoncomputable env n then
          throwError "Noncomputable schedule dependency: {n}"
  let mut declarations : Array Json := #[]
  let mut nodes : Array Json := #[]
  for n in closure env selected.toList do
    let some ci := env.find? n | throwError "Missing {n}"
    let owner := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i.toNat]!.toString
      | none => ""
    let k := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def"
      | .inductInfo _ => "inductive" | _ => "constant"
    nodes := nodes.push <| Json.mkObj [("id",toJson n.toString),("kind",toJson k),
      ("module",toJson owner),("typeRefs",toJson (ci.type.getUsedConstants.map Name.toString)),
      ("bodyRefs",toJson ((((ci.value? true).map Expr.getUsedConstants).getD #[]).map Name.toString))]
    if selected.contains n then
      let ty ← liftTermElabM do return (← Meta.ppExpr ci.type).pretty 88
      let v ← if k == "def" then
        match ci.value? true with
        | some e => liftTermElabM do return Json.str ((← Meta.ppExpr e).pretty 88)
        | none => pure Json.null
        else pure Json.null
      declarations := declarations.push <| Json.mkObj [("name",toJson n.toString),
        ("kind",toJson k),("type",toJson ty),("value",v),("ownerModule",toJson owner)]
  IO.FS.createDirAll "reports"
  IO.FS.writeFile "reports/schedule-map.json" ((Json.mkObj [
    ("declarations",toJson declarations),("nodes",toJson nodes),
    ("checks",Json.mkObj [("scheduleLemmasChecked",toJson true),("noSorryAx",toJson true),
      ("scheduleLemmasMathlibFree",toJson true),("noNativeNoncomputable",toJson true)])]).compress ++ "\n")
  logInfo "PASS: supplied schedules and their validity/equivalence lemmas checked; reader declarations exported"
end ScheduleMapExport
