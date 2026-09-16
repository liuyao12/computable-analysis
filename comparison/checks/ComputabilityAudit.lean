import ComputableAnalysis.CosinePrimitive
import ComputableAnalysis.TrigonometricReadback
import ComputableAnalysis.RotationSeries
import Lean

/-! Checked separately from Mathlib. A noncomputable tag is not the same as
an axiom or a classical proof. Check actual native declaration closures,
report external tags, then require concrete evaluations to compile and run. -/
namespace ComputabilityAudit
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def roots : Array Name := #[
  ``ComputableAnalysis.CosinePrimitive.A,
  ``ComputableAnalysis.CosinePrimitive.pi,
  ``ComputableAnalysis.CosinePrimitive.S,
  ``ComputableAnalysis.CosinePrimitive.C,
  ``ComputableAnalysis.CosinePrimitive.integral,
  ``ComputableAnalysis.CosinePrimitive.viaInequalities,
  ``ComputableAnalysis.CosinePrimitive.viaFTC,
  ``ComputableAnalysis.RotationSeries.rotationExpRaw]

def refs (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++ ((ci.value? true).map Expr.getUsedConstants).getD #[]

partial def closure (env : Environment) (todo : List Name) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n::rest =>
    if seen.contains n then closure env rest seen else
      match env.find? n with
      | none => closure env rest (seen.insert n)
      | some ci => closure env ((refs ci).toList ++ rest) (seen.insert n)

def owner (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!.toString
  | none => ""

run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for root in roots do
    let deps := closure env [root]
    let mut nativeTags : Array String := #[]
    let mut otherTags : Array String := #[]
    let mut count := 0
    for name in deps do
      count := count + 1
      let m := owner env name
      if m.startsWith "Mathlib" then throwError "Native root uses Mathlib: {root} -> {name}"
      if isNoncomputable env name then
        if m.startsWith "ComputableAnalysis" then
          nativeTags := nativeTags.push name.toString
        else otherTags := otherTags.push name.toString
    unless nativeTags.isEmpty do throwError "Native noncomputable dependencies in {root}: {nativeTags}"
    let axioms ← collectAxioms root
    if axioms.contains `sorryAx then throwError "Admitted dependency: {root}"
    rows := rows.push <| Json.mkObj [
      ("root",toJson root.toString),("closureSize",toJson count),
      ("nativeNoncomputableDependencies",toJson nativeTags),
      ("externalNoncomputableTags",toJson otherTags),
      ("axioms",toJson (axioms.map Name.toString))]
  IO.FS.createDirAll "reports"
  IO.FS.writeFile "reports/native-computability.json" ((Json.mkObj [
    ("nativeNoncomputableClosureCheck",toJson true),("nativeMathlibFree",toJson true),
    ("noSorryAx",toJson true),("roots",toJson rows),
    ("scope",toJson "Declared native roots: stored type/body closure. External proof tags and axioms reported separately. Compiled smoke evaluations follow.")]).compress ++ "\n")
  logInfo "PASS: native numerical roots and two native proofs have no native noncomputable declaration dependency"

end ComputabilityAudit

-- These execute data-producing definitions, not proof reductions.
#eval do
  let p := ComputableAnalysis.CosinePrimitive.pi.compute 0
  unless p.lo == 2 && p.hi == 4 do throw <| IO.userError "Unexpected pi box"
  let s := (ComputableAnalysis.CosinePrimitive.S (1/4)).compute 0
  let c := (ComputableAnalysis.CosinePrimitive.C (1/4)).compute 0
  unless s.lo <= s.hi && c.lo <= c.hi do throw <| IO.userError "Unordered circle coordinates"
  let i := (ComputableAnalysis.CosinePrimitive.integral (1/2)
    ⟨by decide +kernel, by decide +kernel⟩).compute 0
  unless i.lo == -1000 && i.hi == 2001/2 do throw <| IO.userError "Unexpected quadrature box"
  IO.println "PASS: compiled rational pi, sine, cosine, and quadrature smoke evaluations"
