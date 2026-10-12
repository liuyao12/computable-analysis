import Lean
import ComputableAnalysis.GeometricCircleODEComparison

open Lean Elab Command
open ComputableAnalysis.GeometricCircleODEComparison
open ComputableAnalysis.GeometricCircleRational

private partial def closure (env : Environment) (name : Name) : StateM NameSet Unit := do
  if (← get).contains name then return
  let mod := env.getModuleIdxFor? name |>.map (fun i => env.allImportedModuleNames[i.toNat]!)
  if !(mod.any (·.toString.startsWith "ComputableAnalysis.")) then return
  modify (·.insert name)
  if let some info := env.find? name then
    for dep in info.type.getUsedConstants do closure env dep
    if let some value := info.value? (allowOpaque := true) then
      for dep in value.getUsedConstants do closure env dep

run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if mod.toString.startsWith "Mathlib" then throwError "Unexpected Mathlib import: {mod}"
  for root in [``ComputableAnalysis.RiemannHilbert.CommonEulerLimit.unique,
      ``angle_valid, ``point_neg, ``point_reciprocal,
      ``geometricSolutionEvidence, ``analyticSolutionEvidence,
      ``geometric_rotation_ode_unique, ``geometric_rotation_all_rational,
      ``geometric_sine_powerSeries, ``geometric_sine_primary_converges,
      ``primary_agreement_on_overlap] do
    let axioms ← collectAxioms root
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {root}"
    logInfo m!"AUDIT {root}: {axioms}"
  for root in [``ComputableAnalysis.GeometricCircleRational.sine,
      ``ComputableAnalysis.GeometricCircleRational.cosine, ``angle, ``geometricPoint] do
    let defs := ((closure env root).run {}).2
    for name in defs.toArray do
      if name.toString.toLower.contains "exponential" ||
          name.toString.startsWith "ComputableAnalysis.ElementaryPowerSeries." then
        throwError "Geometric construction depends on analytic evaluator: {root}: {name}"
  let core := ((closure env ``geometric_rotation_ode_unique).run {}).2
  for required in [``ComputableAnalysis.RiemannHilbert.CommonEulerLimit.unique,
      ``geometricSolutionEvidence, ``analyticSolutionEvidence,
      ``ComputableAnalysis.ElementaryCircleAngle.mesh_error,
      ``ComputableAnalysis.ElementaryCircleAngle.angle_target_error,
      ``ComputableAnalysis.ElementaryCircleAngle.product_endpoint_error] do
    unless core.contains required do throwError "Missing constructed solution evidence: {required}"
  let applied := ((closure env ``geometric_sine_powerSeries).run {}).2
  for required in [``geometric_rotation_ode_unique, ``point_neg, ``point_reciprocal,
      ``ComputableAnalysis.ElementarySineODE.computations_agree_global] do
    unless applied.contains required do throwError "Missing ODE/coverage dependency: {required}"
  for name in applied.toArray do
    if name == ``ComputableAnalysis.ElementaryCircleAngle.exponential_twiceArctangent ||
        name.toString.startsWith "ComputableAnalysis.ElementaryTrigonometricCharts." ||
        name.toString.startsWith "ComputableAnalysis.ElementaryArctangentComparison." then
      throwError "Previous geometric sine agreement reused: {name}"
  logInfo m!"PASS: geometric primary definitions and sector-angle algorithms have no exponential or power-series dependency; actual common-Euler solution evidence, whole-plane oscillator uniqueness and all-rational chart coverage are used; no previous geometric endpoint agreement ({applied.toArray.size} declarations)."
