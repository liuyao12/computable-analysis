import Lean
import ComputableAnalysis.SqrtSecantFoundation
import ComputableAnalysis.SquareRootSecantNewton
import ComputableAnalysis.ArctanInverseCircle

open Lean Elab Command

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
  for root in [``ComputableAnalysis.SquareRootSecantNewton.step_spec,
      ``ComputableAnalysis.SquareRootSecantNewton.sqrtTwo_valid,
      ``ComputableAnalysis.SquareRootSecantNewton.sqrtTwo_equiv_bisection,
      ``ComputableAnalysis.SquareRootSecantNewton.bracket_quadratic,
      ``ComputableAnalysis.SqrtSecantFoundation.derivative_valid_and_equiv,
      ``ComputableAnalysis.SqrtSecantFoundation.positive_segment_hasIntegral,
      ``ComputableAnalysis.SqrtSecantFoundation.ftc,
      ``ComputableAnalysis.ArctanSecantFoundation.derivative_valid_and_equiv,
      ``ComputableAnalysis.ArctanSecantFoundation.hasIntegral,
      ``ComputableAnalysis.ArctanSecantFoundation.ftc,
      ``ComputableAnalysis.ArctanInverseConstruction.inverse_valid,
      ``ComputableAnalysis.ArctanInverseConstruction.rational_forward_target,
      ``ComputableAnalysis.ArctanInverseCircle.sine_valid,
      ``ComputableAnalysis.ArctanInverseCircle.cosine_valid,
      ``ComputableAnalysis.ArctanInverseCircle.quarterSlope_target,
      ``ComputableAnalysis.ArctanInverseCircle.sineQuarter_valid,
      ``ComputableAnalysis.ArctanInverseCircle.cosineQuarter_valid] do
    let axioms ← collectAxioms root
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {root}"
    logInfo m!"AUDIT {root}: {axioms}"
  for root in [``ComputableAnalysis.SquareRootSecantNewton.sqrtTwo,
      ``ComputableAnalysis.ArctanInverseCircle.sine,
      ``ComputableAnalysis.ArctanInverseCircle.cosine,
      ``ComputableAnalysis.ArctanInverseCircle.sineQuarter,
      ``ComputableAnalysis.ArctanInverseCircle.cosineQuarter] do
    let names := ((closure env root).run {}).2
    for name in names.toArray do
      if name.toString.toLower.contains "exponential" ||
          name.toString.startsWith "ComputableAnalysis.ElementaryPowerSeries." then
        throwError "Independent inverse computation uses analytic evaluator: {root}: {name}"
  logInfo m!"PASS: specific inverse computations, secant derivative validity and exact FTC are checked; standard axioms only; primary square-root and inverse-circle computations contain no exponential or power-series foundation."
