import MathlibComparison.CosinePrimitive
import ComputableAnalysis.CosinePrimitiveViaFTC
import ComputableAnalysis.CosinePrimitiveViaInequalities
import ComputableAnalysis.RotationSeries
import Lean

/-! Check the three whole theorem types and their dependency separation.
The graph exporter follows stored types and bodies, not import lists. -/
namespace ThreeProofsAudit
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def roots : Array Name := #[
  ``ComputableAnalysis.CosinePrimitive.viaInequalities,
  ``ComputableAnalysis.CosinePrimitive.viaFTC,
  ``ComputableAnalysis.CosinePrimitive.viaMathlib]

def companions : Array Name := #[
  ``ComputableAnalysis.CosinePrimitive.C,
  ``ComputableAnalysis.RotationSeries.rotationExpRaw_valid,
  ``ComputableAnalysis.GeometricSineConcavity.sineDerivative_valid,
  ``ComputableAnalysis.CosinePrimitive.integral_valid_viaMathlib]

def refs (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++ ((ci.value? true).map Expr.getUsedConstants).getD #[]

partial def closure (env : Environment) (pending : List Name) (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n::rest =>
    if seen.contains n then closure env rest seen
    else
      let next := match env.find? n with | none => [] | some ci => (refs ci).toList
      closure env (next ++ rest) (seen.insert n)

def owner (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!.toString
  | none => ""

partial def treeSize (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
  if let some n := (← get).get? e then return n
  let n ← match e with
    | .app f a => return 1+(← treeSize f)+(← treeSize a)
    | .lam _ t b _ | .forallE _ t b _ => return 1+(← treeSize t)+(← treeSize b)
    | .letE _ t v b _ => return 1+(← treeSize t)+(← treeSize v)+(← treeSize b)
    | .mdata _ b | .proj _ _ b => return 1+(← treeSize b)
    | _ => pure 1
  modify (·.insert e n)
  return n

/-- Display-only declarations are audited and exported without adding them to
any proof's measured closure. The group manifest is shared with the UI export. -/
def displayedNames : IO (Array Name) := do
  let text ← IO.FS.readFile "../blueprint/three-proofs/node-groups.tsv"
  let mut result : Array Name := #[]
  for rawLine in text.splitOn "\n" do
    let line := rawLine.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    let fields := line.splitOn "\t"
    unless fields.length == 4 do
      throw (IO.userError s!"Invalid blueprint group row: {line}")
    result := result.push fields[2]!.toName
  return result

run_cmd do
  let env ← getEnv
  let displayed ← displayedNames
  let infos ← roots.mapM fun n => match env.find? n with
    | some ci => pure ci
    | none => throwError "Missing root {n}"
  liftTermElabM do
    for ci in infos do
      unless ← Meta.isDefEq infos[0]!.type ci.type do
        throwError "Proof types differ: {ci.name}"
  logInfo "PASS: all three complete theorem types are definitionally identical"
  let closures := roots.map (fun n => closure env [n])
  for i in [:3] do
    let deps := closures[i]!
    for j in [:3] do
      if i != j && deps.contains roots[j]! then throwError "Proof {roots[i]!} calls {roots[j]!}"
    if i < 2 then
      for n in deps do
        let m := owner env n
        if m.startsWith "Mathlib" then throwError "Native route depends on {m}: {n}"
  for bad in [
      `ComputableAnalysis.CosineFTC.integral_cosPi_viaInequalities,
      `ComputableAnalysis.CosineFTC.integral_cosPi_viaFTC,
      `ComputableAnalysis.CosineFTC.fixedMesh_overlaps_endpoint,
      `ComputableAnalysis.ConcaveFTC.integral_equiv_endpoint,
      `ComputableAnalysis.GeometricSineDirectBounds.positive_increment_error,
      `ComputableAnalysis.GeometricSineDerivative.sinPi_derivative_explicit] do
    if closures[2]!.contains bad then throwError "Mathlib route reuses forbidden native proof {bad}"
  for required in [``MathlibComparison.cosine_integral_represents,
      ``MathlibComparison.mathlib_cosine_primitive,``MathlibComparison.sine_represents,
      ``MathlibComparison.cosine_represents,``MathlibComparison.piCircleArea_represents] do
    unless closures[2]!.contains required do throwError "Third proof omits bridge {required}"
  logInfo "PASS: native routes are Mathlib-free; the third route uses independent quadrature and value bridges"
  let mut metrics : Array Json := #[]
  for i in [:3] do
    let n := roots[i]!
    let axs ← collectAxioms n
    if axs.contains `sorryAx then throwError "Admitted proof in {n}"
    let mut counts : Std.HashMap String Nat := {}
    for dep in closures[i]! do
      let m := owner env dep
      let bucket := if m.startsWith "ComputableAnalysis" then "native"
        else if m.startsWith "MathlibComparison" then "bridge"
        else if m.startsWith "Mathlib." then "mathlib" else "leanOrOther"
      counts := counts.insert bucket (counts.getD bucket 0 + 1)
    let body := (infos[i]!.value? true).getD (.sort .zero)
    let (size,memo) := (treeSize body).run {}
    metrics := metrics.push <| Json.mkObj [
      ("proof",toJson n.toString),("bodyTreeNodes",toJson size),("bodyDagNodes",toJson memo.size),
      ("native",toJson (counts.getD "native" 0)),("bridge",toJson (counts.getD "bridge" 0)),
      ("mathlib",toJson (counts.getD "mathlib" 0)),("leanOrOther",toJson (counts.getD "leanOrOther" 0)),
      ("axioms",toJson (axs.map Name.toString))]
  for n in companions ++ displayed do
    let axs ← collectAxioms n
    if axs.contains `sorryAx then throwError "Admitted proof in companion {n}"
  logInfo "PASS: all proof and companion axiom audits exclude sorryAx"
  let all := closure env (roots ++ companions ++ displayed).toList
  let mut nodes : Array Json := #[]
  for n in all do
    let some ci := env.find? n | throwError "Missing reference {n}"
    let m := owner env n
    let range ← findDeclarationRanges? n
    let lines := match range with
      | none => Json.null
      | some r => Json.mkObj [("start",toJson r.selectionRange.pos.line),("end",toJson r.range.endPos.line)]
    nodes := nodes.push <| Json.mkObj [
      ("id",toJson n.toString),("name",toJson ((privateToUserName? n).getD n).toString),
      ("module",toJson m),("sourceRange",lines),
      ("refs",toJson ((refs ci).map Name.toString)),
      ("routes",toJson ((List.range 3).filter (fun i => closures[i]!.contains n))),
      ("kind",toJson (match ci with | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | .axiomInfo _ => "axiom" | _ => "other"))]
  let out := Json.mkObj [
    ("schemaVersion",toJson (1:Nat)),("leanVersion",toJson Lean.versionString),
    ("roots",toJson (roots.map Name.toString)),("metrics",toJson metrics),("nodes",toJson nodes),
    ("checks",Json.mkObj [("sameStatement",toJson true),("independentRoutes",toJson true),
      ("nativeMathlibFree",toJson true),("thirdUsesValueAndQuadratureBridges",toJson true),
      ("noSorryAx",toJson true)])]
  let path := (← IO.getEnv "THREE_PROOFS_REPORT").getD "reports/three-proofs.json"
  IO.FS.writeFile path (out.compress ++ "\n")
  logInfo m!"Exported {nodes.size} reference nodes to {path}"

end ThreeProofsAudit
