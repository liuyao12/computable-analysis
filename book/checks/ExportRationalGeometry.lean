import ComputableAnalysis.QuarterCircleGeometry
import Lean

/-! Checked declarations for the revised opening of Chapter 2. -/
namespace RationalGeometryExport
open Lean Elab Command ComputableAnalysis
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def selected : Array Name := #[
  ``RationalGeometry.Point, ``RationalGeometry.Polygon, ``RationalGeometry.det,
  ``RationalGeometry.AreaForm, ``RationalGeometry.determinantAreaForm,
  ``RationalGeometry.AreaForm.unique,
  ``RationalGeometry.parallelogramArea, ``RationalGeometry.triangleArea,
  ``RationalGeometry.triangle_boundary, ``RationalGeometry.triangle_subdivision,
  ``RationalGeometry.edgeArea, ``RationalGeometry.walk, ``RationalGeometry.cycleSum,
  ``RationalGeometry.area, ``RationalGeometry.startAt,
  ``RationalGeometry.area_startAt, ``RationalGeometry.fanArea,
  ``RationalGeometry.fanArea_eq_area, ``RationalGeometry.fanArea_startAt,
  ``RationalGeometry.fanFrom, ``RationalGeometry.triangulationArea,
  ``RationalGeometry.triangulationArea_eq_area, ``RationalGeometry.triangulationArea_startAt,
  ``RationalGeometry.area_reverse, ``RationalGeometry.AffineMap,
  ``RationalGeometry.AffineMap.apply, ``RationalGeometry.AffineMap.area_apply,
  ``RationalGeometry.AffineMap.Orthogonal,
  ``RationalGeometry.AffineMap.determinant_sq_of_orthogonal,
  ``RationalGeometry.area_translation, ``RationalGeometry.area_homothety,
  ``RationalGeometry.Point3, ``RationalGeometry.det3,
  ``RationalGeometry.tetrahedronVolume, ``RationalGeometry.tetrahedron_swap,
  ``RationalGeometry.tetrahedron_subdivision, ``RationalGeometry.tetrahedron_scale,
  ``QuarterCircleGeometry.raw, ``QuarterCircleGeometry.raw_valid,
  ``QuarterCircleGeometry.raw_compute, ``QuarterCircleGeometry.raw_width,
  ``QuarterCircleGeometry.point, ``QuarterCircleGeometry.innerPolygon,
  ``QuarterCircleGeometry.outerPolygon, ``QuarterCircleGeometry.inner_area_nonneg,
  ``QuarterCircleGeometry.outer_area_nonneg, ``QuarterCircleGeometry.area_legacy,
  ``QuarterCircleGeometry.raw_compute_polygon_areas,
  ``QuarterCircleGeometry.raw_compute_any_fans]

def refs (ci : ConstantInfo) : Array Name := ci.type.getUsedConstants ++
  ((ci.value? true).map Expr.getUsedConstants).getD #[]

partial def closure (env : Environment) (pending : List Name) (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env rest seen else
      let more := match env.find? n with | none => [] | some ci => (refs ci).toList
      closure env (more ++ rest) (seen.insert n)

def owner (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!.toString
  | none => ""

open RationalGeometry in
example : area [⟨0,0⟩,⟨1,0⟩,⟨1,1⟩,⟨0,1⟩] = 1 := by decide +kernel
open RationalGeometry in
example : area [⟨0,0⟩,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩] = 0 := by decide +kernel
open RationalGeometry in
example : area [⟨0,0⟩,⟨2,0⟩,⟨1,1⟩,⟨2,2⟩,⟨0,2⟩] = 3 := by decide +kernel
example : QuarterCircleGeometry.raw.compute 0 = {lo:=1/2,hi:=1} := by decide +kernel
example : QuarterCircleGeometry.raw.compute 1 = {lo:=7/10,hi:=5/6} := by decide +kernel

run_cmd do
  let env ← getEnv
  let mut audits : Array Json := #[]
  let mut roots : Array Name := #[]
  for n in selected do
    if let some (.thmInfo _) := env.find? n then roots := roots.push n
  for root in roots do
    let deps := closure env [root]
    for dep in deps do
      let m := owner env dep
      if m.startsWith "Mathlib" then throwError "Unexpected Mathlib dependency {dep}"
      if m.startsWith "ComputableAnalysis" && isNoncomputable env dep then
        throwError "Noncomputable dependency {dep}"
      if root.toString.startsWith "ComputableAnalysis.RationalGeometry" &&
          (dep.toString.startsWith "ComputableAnalysis.RealRaw" ||
           dep.toString.startsWith "ComputableAnalysis.RationalCircle" ||
           dep.toString.startsWith "ComputableAnalysis.Integral" ||
           dep.toString.startsWith "ComputableAnalysis.ArctanGeometry") then
        throwError "Finite geometry depends on analysis {dep}"
    let axs ← collectAxioms root
    if axs.contains `sorryAx then throwError "Admitted proof {root}"
    audits := audits.push <| Json.mkObj [("root",toJson root.toString),
      ("axioms",toJson (axs.map Name.toString))]
  let validity := closure env [``QuarterCircleGeometry.raw_valid]
  for dep in validity do
    if dep.toString.startsWith "ComputableAnalysis.RationalGeometry" then
      throwError "Numerical validity borrows the new geometric interpretation {dep}"
  let all := closure env selected.toList
  let mut declarations : Array Json := #[]
  let mut nodes : Array Json := #[]
  for n in all do
    let some ci := env.find? n | throwError "Missing declaration {n}"
    let kind := match ci with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "def"
      | .inductInfo _ => "inductive"
      | _ => "constant"
    nodes := nodes.push <| Json.mkObj [("id",toJson n.toString),("kind",toJson kind),
      ("module",toJson (owner env n)),("typeRefs",toJson (ci.type.getUsedConstants.map Name.toString)),
      ("bodyRefs",toJson ((((ci.value? true).map Expr.getUsedConstants).getD #[]).map Name.toString))]
    if selected.contains n then
      let ty ← liftTermElabM do return (← Meta.ppExpr ci.type).pretty 88
      let value ← if kind == "def" then
        match ci.value? true with
        | some v => liftTermElabM do return Json.str ((← Meta.ppExpr v).pretty 88)
        | none => pure Json.null
        else pure Json.null
      declarations := declarations.push <| Json.mkObj [("name",toJson n.toString),
        ("kind",toJson kind),("type",toJson ty),("value",value),("ownerModule",toJson (owner env n))]
  let stages := (List.range 5).map fun n =>
    let box := QuarterCircleGeometry.raw.compute n
    Json.mkObj [("stage",toJson n),("lower",toJson (toString box.lo)),
      ("upper",toJson (toString box.hi)),("gap",toJson (toString box.width))]
  IO.FS.createDirAll "geometry-reports"
  IO.FS.writeFile "geometry-reports/rational-geometry.json" ((Json.mkObj [
    ("leanVersion",toJson Lean.versionString),("audits",toJson audits),
    ("declarations",toJson declarations),("nodes",toJson nodes),("stages",toJson stages),
    ("checks",Json.mkObj [("noSorryAx",toJson true),("noMathlib",toJson true),
      ("noNativeNoncomputable",toJson true),("finiteGeometryIndependentOfAnalysis",toJson true),
      ("validityIndependentOfPolygonInterpretation",toJson true),
      ("cyclicAndFanInvariance",toJson true),("exactQuarterCircleStageBridge",toJson true),
      ("sharpQuarterCircleGap",toJson true)])]).compress ++ "\n")
  logInfo m!"PASS: {roots.size} checked theorem roots; {declarations.size} exact declaration cards; literal quarter-circle stages exported"
end RationalGeometryExport
