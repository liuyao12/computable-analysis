import Lean
import ComputableAnalysis.ElementarySineODEComparison
import ComputableAnalysis.GeometricCircleODEComparison

/-! Export checked declaration dependencies for the interactive sine route.
Proof-body constants and theorem-type constants remain separately labelled. -/
open Lean Elab Command
open ComputableAnalysis.ElementarySineODE
open ComputableAnalysis.ElementarySineComparison
open ComputableAnalysis.RiemannHilbert.MatrixExponential

private def projectModule (env : Environment) (name : Name) : Option Name :=
  env.getModuleIdxFor? name |>.map (fun i => env.allImportedModuleNames[i.toNat]!)

private def isProject (env : Environment) (name : Name) : Bool :=
  (projectModule env name).any (·.toString.startsWith "ComputableAnalysis.")

private partial def closure (env : Environment) (name : Name) : StateM NameSet Unit := do
  if (← get).contains name then return
  if !isProject env name then return
  modify (·.insert name)
  if let some info := env.find? name then
    for dep in info.type.getUsedConstants do closure env dep
    if let some value := info.value? (allowOpaque := true) then
      for dep in value.getUsedConstants do closure env dep

private def namesJson (env : Environment) (names : Array Name) : Json :=
  Json.arr <| (names.filter (isProject env)).qsort Name.lt |>.map
    (fun n => Json.str n.toString)

run_cmd do
  let env ← getEnv
  let roots := [``ComputableAnalysis.RiemannHilbert.CommonEulerLimit.unique,
    ``ComputableAnalysis.GeometricCircleRational.angle_valid,
    ``ComputableAnalysis.GeometricCircleRational.sine,
    ``ComputableAnalysis.GeometricCircleRational.cosine,
    ``ComputableAnalysis.GeometricCircleRational.sine_valid,
    ``ComputableAnalysis.GeometricCircleRational.cosine_valid,
    ``ComputableAnalysis.GeometricCircleRational.point_neg,
    ``ComputableAnalysis.GeometricCircleRational.point_reciprocal,
    ``ComputableAnalysis.GeometricCircleODEComparison.geometricSolutionEvidence,
    ``ComputableAnalysis.GeometricCircleODEComparison.analyticSolutionEvidence,
    ``ComputableAnalysis.GeometricCircleODEComparison.geometric_rotation_ode_unique,
    ``ComputableAnalysis.GeometricCircleODEComparison.geometric_rotation_all_rational,
    ``ComputableAnalysis.GeometricCircleODEComparison.geometric_sine_powerSeries,
    ``ComputableAnalysis.GeometricCircleODEComparison.geometric_sine_primary_converges,
    ``ComputableAnalysis.GeometricCircleODEComparison.primary_agreement_on_overlap,
    ``ComputableAnalysis.GeometricRotationODE.pointComplexDerivative_eq_angularVelocity_mul_point,
    ``ComputableAnalysis.GeometricRotationODE.point_hasComplexDerivativeOnUnit,
    ``constant_ode_path_unique, ``constant_ode_entire_unique,
    ``sine_derivative, ``cosine_derivative, ``exponentialVector_ode,
    ``seriesVector_ode, ``exponentialVector_initial, ``seriesVector_initial,
    ``computations_agree_global, ``seriesVector_reparametrization,
    ``sinPi_powerSeries_global, ``powerSeries_primary_agrees, ``sinPi_primary_agrees,
    ``powerSeries_primary_converges, ``sinPi_primary_converges, ``sinPi_primary_ode_comparison,
    ``powerSeries_rational_agrees_derived, ``sinPi_agrees_derived_powerSeries,
    ``sinPi_powerSeries_agrees_at_coordinates,
    ``ComputableAnalysis.ElementaryPowerSeries.sineValue_realAxis_agrees,
    ``ComputableAnalysis.ElementaryPowerSeries.sineValue_agrees,
    ``ComputableAnalysis.ElementaryPowerSeries.imaginaryPrefix_pair,
    ``ComputableAnalysis.ModularForms.entireExponential_legacy_lift,
    ``ComputableAnalysis.ModularForms.entireExponential_derivative_value,
    ``ComputableAnalysis.RiemannHilbert.ConstructedSystemODE.solution_unique_local,
    ``ComputableAnalysis.RiemannHilbert.DomainVectorFunctions.zero_derivative_path_constant]
  let names : NameSet := ((do for root in roots do closure env root).run {}).2
  let mut entries := []
  for name in names.toArray.qsort Name.lt do
    if let some info := env.find? name then
      let proofDeps := match info.value? (allowOpaque := true) with
        | some value => value.getUsedConstants
        | none => #[]
      let kind := match info with
        | .thmInfo _ => "theorem"
        | .axiomInfo _ => "axiom"
        | _ => "definition"
      entries := (name.toString, Json.mkObj [
        ("kind",Json.str kind),
        ("module",Json.str ((projectModule env name).getD .anonymous).toString),
        ("proofDependencies",namesJson env proofDeps),
        ("typeDependencies",namesJson env info.type.getUsedConstants)]) :: entries
  let output := Json.mkObj [
    ("roots",namesJson env roots.toArray),
    ("declarations",Json.mkObj entries.reverse),
    ("scope",Json.str "Project constants extracted from checked Lean proof bodies and declaration types. Definition dependencies include their executable bodies. These are distinct from module imports and from curated mathematical arrows.")]
  liftIO <| IO.FS.writeFile "book/modular-dependencies/sine-proof-dependencies.json" output.compress
  logInfo m!"Exported {names.toArray.size} checked project declarations."
