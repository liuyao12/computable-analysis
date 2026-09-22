import ComputableAnalysis.QuadratureAdapters
import Lean

namespace QuadratureAudit
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def roots : Array Name := #[
  ``ComputableAnalysis.ClosedArctanInverse.meshRadius_le,
  ``ComputableAnalysis.RationalSampleLimits.equiv_of_close,
  ``ComputableAnalysis.TaggedQuadrature.average_close,
  ``ComputableAnalysis.TaggedQuadrature.lipschitz_tag_error,
  ``ComputableAnalysis.TaggedQuadrature.decreasing_bounds,
  ``ComputableAnalysis.Quadrature.Certificate.equiv_of_pointwise,
  ``ComputableAnalysis.Quadrature.Certificate.congr_function,
  ``ComputableAnalysis.Quadrature.Certificate.value_of_exact_rule,
  ``ComputableAnalysis.Quadrature.Certificate.zero_interval,
  ``ComputableAnalysis.Quadrature.Certificate.add,
  ``ComputableAnalysis.Quadrature.Certificate.scale,
  ``ComputableAnalysis.Quadrature.constant,
  ``ComputableAnalysis.Quadrature.ofRationalLipschitz,
  ``ComputableAnalysis.Quadrature.ofMonotoneSamples,
  ``ComputableAnalysis.Quadrature.rationalLipschitzFor,
  ``ComputableAnalysis.Quadrature.ConstructionFor.equiv,
  ``ComputableAnalysis.RationalLipschitzIntegral.raw,
  ``ComputableAnalysis.RationalLipschitzIntegral.valid]

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
    let mut modules : Std.HashSet String := {}
    for name in deps do
      let m := owner env name
      if m.startsWith "Mathlib" then throwError "Mathlib dependency: {root} -> {name}"
      if m.startsWith "ComputableAnalysis" && isNoncomputable env name then
        throwError "Native noncomputable dependency: {root} -> {name}"
      if m.startsWith "ComputableAnalysis" then modules := modules.insert m
      if m == "ComputableAnalysis.ClockTrigonometry" || m == "ComputableAnalysis.ClosedArctanInverse" then
        throwError "Generic quadrature depends on trigonometry: {root} -> {name}"
    let axs ← collectAxioms root
    if axs.contains `sorryAx then throwError "Admitted dependency: {root}"
    let some ci := env.find? root | throwError "Missing root {root}"
    let ty ← liftTermElabM do return (← Meta.ppExpr ci.type).pretty 100
    rows := rows.push <| Json.mkObj [
      ("name",toJson root.toString),("type",toJson ty),
      ("declaration_count",toJson deps.size),("native_modules",toJson modules.toArray),
      ("axioms",toJson (axs.map Name.toString))]
  for root in [``ComputableAnalysis.RationalLipschitzIntegral.raw,
      ``ComputableAnalysis.RationalLipschitzIntegral.valid] do
    for name in closure env [root] do
      if name.toString.startsWith "ComputableAnalysis.Quadrature." then
        throwError "Old evaluator or validity borrows the new semantic conclusion: {root} -> {name}"
  IO.FS.createDirAll ".lake/cleanup"
  IO.FS.writeFile ".lake/cleanup/quadrature-audit.json" ((Json.mkObj [
    ("mathlib_free",toJson true),("no_native_noncomputable_dependencies",toJson true),
    ("no_sorryAx",toJson true),("no_trigonometry_dependency",toJson true),
    ("independent_existing_evaluator_and_validity",toJson true),
    ("roots",toJson rows)]).pretty ++ "\n")
  logInfo "PASS: 18 roots; exact types and axioms; no Mathlib/trigonometry; independent evaluator and validity"
end QuadratureAudit
