import ComputableAnalysis.TrigonometricReadback
import MathlibComparison.CosinePrimitive
import ComputableAnalysis.CosinePrimitiveViaFTC
import ComputableAnalysis.CosinePrimitiveViaInequalities
import ComputableAnalysis.RotationSeries
import Lean

/-! Read the same declaration names as the blueprint and export their actual
elaborated types. This is display tooling; no mathematical declaration changes.
The group manifest curates several declarations per mathematical node.
Only explicitly selected definitions include a body. Proof bodies are omitted. -/
namespace BlueprintStatementExport
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def valueNames : List Name := [
  ``ComputableAnalysis.CosinePrimitive.A,
  ``ComputableAnalysis.CosinePrimitive.pi,
  ``ComputableAnalysis.CosinePrimitive.S,
  ``ComputableAnalysis.CosinePrimitive.C,
  ``ComputableAnalysis.CosinePrimitive.Statement,
  ``ComputableAnalysis.CosinePrimitive.integral,
  ``MathlibComparison.Represents,
  ``Real.pi]

run_cmd do
  let text ← IO.FS.readFile "../blueprint/src/06-three-cosine-proofs.tex"
  let groups ← IO.FS.readFile "../blueprint/three-proofs/node-groups.tsv"
  let env ← getEnv
  let mut requested : Array Name := #[]
  let mut includeBody : NameSet := {}
  for name in valueNames do includeBody := includeBody.insert name
  for chunk in (text.splitOn "\\lean{").drop 1 do
    for word in ((chunk.splitOn "}").head!).splitOn "," do
      requested := requested.push word.trimAscii.toString.toName
  for rawLine in groups.splitOn "\n" do
    let line := rawLine.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    let fields := line.splitOn "\t"
    unless fields.length == 4 do throwError "Invalid blueprint group row: {line}"
    let name := fields[2]!.toName
    requested := requested.push name
    if fields[3]! == "yes" then includeBody := includeBody.insert name
  let mut seen : NameSet := {}
  let mut declarations : Array Json := #[]
  for name in requested do
    unless seen.contains name do
      seen := seen.insert name
      let some ci := env.find? name | throwError "Missing blueprint declaration {name}"
      let ty ← liftTermElabM do
        let f ← Meta.ppExpr ci.type
        return f.pretty 88
      let isDefinition := match ci with | .defnInfo _ => true | _ => false
      let value ← if includeBody.contains name && isDefinition then
        match ci.value? true with
        | some v => liftTermElabM do
            let f ← Meta.ppExpr v
            return Json.str (f.pretty 88)
        | none => pure Json.null
      else pure Json.null
      let kind := match ci with
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "def"
        | .axiomInfo _ => "axiom"
        | .inductInfo _ => "inductive"
        | _ => "constant"
      declarations := declarations.push <| Json.mkObj [
        ("name",toJson name.toString), ("kind",toJson kind),
        ("type",toJson ty), ("value",value),
        ("typeRefs",toJson (ci.type.getUsedConstants.map Name.toString))]
  IO.FS.createDirAll "reports"
  IO.FS.writeFile "reports/blueprint-statements.json"
    ((Json.mkObj [("leanVersion",toJson Lean.versionString),
      ("declarations",toJson declarations)]).compress ++ "\n")
  logInfo m!"Exported {declarations.size} checked Lean statements for blueprint node boxes"

end BlueprintStatementExport
