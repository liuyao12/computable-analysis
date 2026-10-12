import Lean
import ComputableAnalysis.ElementarySineODEComparison

open Lean Elab Command
open ComputableAnalysis.ElementarySineODE
open ComputableAnalysis.RiemannHilbert.MatrixExponential

private partial def closure (env : Environment) (name : Name) : StateM NameSet Unit := do
  if (← get).contains name then return
  if !name.toString.startsWith "ComputableAnalysis." then return
  modify (·.insert name)
  if let some info := env.find? name then
    for dep in info.type.getUsedConstants do closure env dep
    if let some value := info.value? (allowOpaque := true) then
      for dep in value.getUsedConstants do closure env dep

run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if mod.toString.startsWith "Mathlib" then throwError "Unexpected Mathlib import: {mod}"
  for root in [``constant_ode_path_unique, ``constant_ode_entire_unique,
      ``sine_derivative, ``cosine_derivative, ``exponentialVector_ode,
      ``seriesVector_ode, ``exponentialVector_initial, ``seriesVector_initial,
      ``computations_agree_global, ``seriesVector_reparametrization,
      ``sinPi_powerSeries_global, ``powerSeries_primary_agrees, ``sinPi_primary_agrees,
      ``powerSeries_primary_converges, ``sinPi_primary_converges, ``sinPi_primary_ode_comparison] do
    let axioms ← collectAxioms root
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {root}"
    logInfo m!"AUDIT {root}: {axioms}"
  let core := ((closure env ``computations_agree_global).run {}).2
  for required in [``exponentialVector_ode, ``seriesVector_ode,
      ``exponentialVector_initial, ``seriesVector_initial, ``constant_ode_entire_unique,
      ``constant_ode_path_unique,
      ``ComputableAnalysis.RiemannHilbert.DomainVectorFunctions.zero_derivative_path_constant] do
    unless core.contains required do throwError "Missing core dependency: {required}"
  for name in core.toArray do
    if name.toString.startsWith "ComputableAnalysis.ElementarySineComparison." ||
        name.toString.startsWith "ComputableAnalysis.ElementarySeriesComparisons." ||
        name == ``ComputableAnalysis.ElementaryPowerSeries.sineValue_agrees then
      throwError "Circular sine agreement dependency: {name}"
  let applied := ((closure env ``sinPi_primary_ode_comparison).run {}).2
  unless applied.contains ``computations_agree_global do
    throwError "Primary comparison does not use global ODE comparison"
  logInfo m!"PASS: actual solution laws and initial values, global path coverage, no earlier sine identity in ODE core ({core.toArray.size} declarations); primary comparison uses ODE core."
