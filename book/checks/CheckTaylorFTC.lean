import ComputableAnalysis.TaylorReciprocal
import Lean

/-! Check actual stored declaration dependencies, not just source imports. -/
namespace TaylorFTCAudit
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def roots : Array Name := #[
  ``ComputableAnalysis.TaylorCancellation.polynomial_error_bound,
  ``ComputableAnalysis.TaylorFTC.weightModel,
  ``ComputableAnalysis.TaylorFTC.primitiveModel,
  ``ComputableAnalysis.TaylorFTC.integral_remainder,
  ``ComputableAnalysis.TaylorFTC.remainder_bound,
  ``ComputableAnalysis.TaylorFTC.approximation_intervals,
  ``ComputableAnalysis.TaylorFTC.integral_remainder_equiv,
  ``ComputableAnalysis.TaylorReciprocal.derivativeModel,
  ``ComputableAnalysis.TaylorReciprocal.remainderIntegral,
  ``ComputableAnalysis.TaylorReciprocal.remainderIntegral_valid,
  ``ComputableAnalysis.TaylorReciprocal.polynomial_value,
  ``ComputableAnalysis.TaylorReciprocal.remainderIntegral_evaluation]

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
    let mut names : Array String := #[]
    for name in deps do
      let m := owner env name
      if m.startsWith "Mathlib" then throwError "Native theorem uses Mathlib: {root} -> {name}"
      if m.startsWith "ComputableAnalysis" && isNoncomputable env name then
        throwError "Native noncomputable dependency: {root} -> {name}"
      if m.startsWith "ComputableAnalysis" then
        modules := modules.insert m
        names := names.push name.toString
    let axs ← collectAxioms root
    if axs.contains `sorryAx then throwError "Admitted dependency: {root}"
    let some ci := env.find? root | throwError "Missing root {root}"
    let ty ← liftTermElabM do return (← Meta.ppExpr ci.type).pretty 100
    rows := rows.push <| Json.mkObj [
      ("name",toJson root.toString),("type",toJson ty),
      ("declarationCount",toJson deps.size),
      ("nativeModules",toJson modules.toArray),
      ("nativeDeclarations",toJson names),
      ("axioms",toJson (axs.map Name.toString))]
  for root in [``ComputableAnalysis.TaylorReciprocal.remainderIntegral,
      ``ComputableAnalysis.TaylorReciprocal.remainderIntegral_valid] do
    let deps := closure env [root]
    for name in deps do
      if name.toString.startsWith "ComputableAnalysis.TaylorFTC." then
        throwError "Quadrature or validity borrows Taylor theorem: {root} -> {name}"
  let edeps := closure env [``ComputableAnalysis.TaylorReciprocal.remainderIntegral_evaluation]
  unless edeps.contains ``ComputableAnalysis.TaylorFTC.integral_remainder do
    throwError "Nonpolynomial example failed to use the new analytic Taylor theorem"
  unless edeps.contains ``ComputableAnalysis.FiniteSampleCalculus.finite_telescope do
    throwError "Nonpolynomial example failed to use the existing finite FTC"
  IO.FS.createDirAll "reports"
  IO.FS.writeFile "reports/taylor-ftc-audit.json" ((Json.mkObj [
    ("nativeMathlibFree",toJson true),("noNativeNoncomputableDependencies",toJson true),
    ("noSorryAx",toJson true),("independentQuadratureAndValidity",toJson true),
    ("exampleUsesTaylorAndExistingFTC",toJson true),("mathlibComparisonAdded",toJson false),
    ("roots",toJson rows)]).pretty ++ "\n")
  logInfo "PASS: arbitrary-order native Taylor, exact interval statements, independent quadrature and nonpolynomial evaluation"
end TaylorFTCAudit

#eval do
  for n in [0,1,2,4] do
    let p := ComputableAnalysis.TaylorFTC.polynomial
      ComputableAnalysis.TaylorReciprocal.derivatives 0 1 n 0
    let expected := (1/2:Rat)^(n+1)
    unless p + expected == 1 do throw <| IO.userError "Incorrect Taylor polynomial"
    let box := (ComputableAnalysis.TaylorReciprocal.remainderIntegral n).compute 5
    unless box.lo <= expected && expected <= box.hi do
      throw <| IO.userError "Quadrature output misses proved remainder"
    IO.println s!"degree {n}: polynomial={p}, remainder={expected}, quadrature box=[{box.lo},{box.hi}]"
