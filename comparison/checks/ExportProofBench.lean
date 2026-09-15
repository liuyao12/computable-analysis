import MathlibComparison.CosinePrimitive
import ComputableAnalysis.CosinePrimitiveViaFTC
import ComputableAnalysis.CosinePrimitiveViaInequalities
import MathlibComparison.ProofBenchExamples
import Lean

/-! Reusable, manifest-driven proof measurement. No production theorem imports
this tool. Every alternative must have the same complete theorem type. Stored
types and bodies, including opaque values, determine the measured graph.
Display-only blueprint declarations are deliberately NOT measurement roots. -/
namespace ProofBenchExport
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure Entry where
  caseId : String
  route : String
  root : Name
  native : Bool

def readEntries : IO (Array Entry) := do
  let path := (← IO.getEnv "PROOF_BENCH_MANIFEST").getD "proof-bench/cases.tsv"
  let text ← IO.FS.readFile path
  let mut result := #[]
  for line in text.splitOn "\n" do
    if line.trimAscii.toString.isEmpty || line.startsWith "#" then continue
    let fs := line.splitOn "\t"
    unless fs.length == 4 && (fs[3]! == "native" || fs[3]! == "mathlib") do
      throw (IO.userError s!"Invalid proof benchmark row: {line}")
    result := result.push ⟨fs[0]!, fs[1]!, fs[2]!.toName, fs[3]! == "native"⟩
  return result

def references (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++ ((ci.value? true).map Expr.getUsedConstants).getD #[]

partial def closure (env : Environment) (todo : List Name) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env rest seen else
      let next := match env.find? n with | none => [] | some ci => (references ci).toList
      closure env (next ++ rest) (seen.insert n)

/-- Tree occurrences with multiplicity; memo cardinality counts structurally
unique subexpressions within this ONE body. Constants are not unfolded. -/
partial def size (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
  if let some n := (← get).get? e then return n
  let n ← match e with
    | .app f a => return 1 + (← size f) + (← size a)
    | .lam _ t b _ | .forallE _ t b _ => return 1 + (← size t) + (← size b)
    | .letE _ t v b _ => return 1 + (← size t) + (← size v) + (← size b)
    | .mdata _ b | .proj _ _ b => return 1 + (← size b)
    | _ => pure 1
  modify (·.insert e n)
  return n

def sizes (e : Expr) : Nat × Nat :=
  let (n, memo) := (size e).run {}
  (n, memo.size)

def moduleName (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!.toString
  | none => ""

def kind (ci : ConstantInfo) : String := match ci with
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

run_cmd do
  let entries ← readEntries
  unless entries.size > 0 do throwError "Empty proof benchmark"
  let env ← getEnv
  let mut cases : Std.HashMap String ConstantInfo := {}
  let mut keys : Std.HashSet String := {}
  let mut roots : Array Json := #[]
  for e in entries do
    let key := e.caseId ++ "/" ++ e.route
    if keys.contains key then throwError "Duplicate case/route: {key}"
    keys := keys.insert key
    let some ci := env.find? e.root | throwError "Missing theorem: {e.root}"
    unless (match ci with | .thmInfo _ => true | _ => false) do
      throwError "Not a theorem: {e.root}"
    if let some previous := cases[e.caseId]? then
      liftTermElabM do
        unless ← Meta.isDefEq previous.type ci.type do
          throwError "Different complete theorem types in {e.caseId}: {previous.name}, {e.root}"
    else cases := cases.insert e.caseId ci
    let deps := closure env [e.root]
    for other in entries do
      if other.caseId == e.caseId && other.root != e.root && deps.contains other.root then
        throwError "{e.root} calls its alternative {other.root}"
    if e.native then
      for dep in deps do
        if (moduleName env dep).startsWith "Mathlib" then
          throwError "Native route {e.root} depends on {dep}"
    let axioms ← collectAxioms e.root
    if axioms.contains `sorryAx then throwError "Admitted proof: {e.root}"
    let ty ← liftTermElabM do return (← Meta.ppExpr ci.type).pretty 100
    roots := roots.push <| Json.mkObj [
      ("case",toJson e.caseId), ("route",toJson e.route),
      ("root",toJson e.root.toString), ("native",toJson e.native),
      ("type",toJson ty), ("axioms",toJson (axioms.map Name.toString))]
  logInfo m!"PASS: {entries.size} proof declarations; identical types within each case, separate alternatives, native boundary, no sorryAx"
  let all := closure env (entries.map (·.root)).toList
  let mut nodes : Array Json := #[]
  for name in all do
    let some ci := env.find? name | throwError "Unknown dependency {name}"
    let ts := sizes ci.type
    let bs := ((ci.value? true).map sizes).getD (0,0)
    let range ← findDeclarationRanges? name
    let lines := match range with
      | none => Json.null
      | some r => Json.mkObj [
          ("start",toJson r.range.pos.line), ("end",toJson r.range.endPos.line)]
    nodes := nodes.push <| Json.mkObj [
      ("id",toJson name.toString),
      ("name",toJson ((privateToUserName? name).getD name).toString),
      ("module",toJson (moduleName env name)), ("kind",toJson (kind ci)),
      ("typeRefs",toJson (ci.type.getUsedConstants.map Name.toString)),
      ("bodyRefs",toJson (((ci.value? true).map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("typeTree",toJson ts.1), ("typeDag",toJson ts.2),
      ("bodyTree",toJson bs.1), ("bodyDag",toJson bs.2), ("sourceRange",lines)]
  let out := Json.mkObj [
    ("schemaVersion",toJson (1:Nat)), ("leanVersion",toJson Lean.versionString),
    ("checks",Json.mkObj [("sameTypes",toJson true), ("noAlternativeReuse",toJson true),
      ("nativeBoundary",toJson true), ("noSorryAx",toJson true)]),
    ("roots",toJson roots), ("nodes",toJson nodes)]
  IO.FS.createDirAll "reports"
  let path := (← IO.getEnv "PROOF_BENCH_OUTPUT").getD "reports/proof-bench-raw.json"
  IO.FS.writeFile path (out.compress ++ "\n")
  logInfo m!"Exported full sizes of {nodes.size} declarations to {path}"

end ProofBenchExport
