import Lean
import ComputableAnalysis.BracketDerivativeExamples
import ComputableAnalysis.ParametrizedFoundationExamples
import ComputableAnalysis.SqrtSecantFoundation
import ComputableAnalysis.SquareRootSecantNewton
import ComputableAnalysis.ArctanInverseCircle

/-! Export checked declaration dependencies for the opening-chapter construction map.
Proof-body constants and theorem-type constants remain separately labelled. -/
open Lean Elab Command

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
  let roots := [
    ``ComputableAnalysis.RawLimit.HasEnclosureValue.unique,
    ``ComputableAnalysis.RawLimit.HasEnclosureValue.congr_value,
    ``ComputableAnalysis.RawLimit.parametrizedLimit_iff,
    ``ComputableAnalysis.RawLimit.HasParametrizedLimit.unique,
    ``ComputableAnalysis.RawLimit.alternating_no_parametrizedLimit,
    ``ComputableAnalysis.RawLimit.prefix_valid,
    ``ComputableAnalysis.RawLimit.prefix_hasEnclosureValue,
    ``ComputableAnalysis.RawLimit.enclosureValue_iff,
    ``ComputableAnalysis.BracketDerivative.hasDerivative_iff_secantLimits,
    ``ComputableAnalysis.BracketDerivative.outerDerivative_hasDerivative,
    ``ComputableAnalysis.BracketContinuity.unique,
    ``ComputableAnalysis.BracketContinuity.bracket_values_equiv,
    ``ComputableAnalysis.BracketContinuity.exists_continuousAt_of_enclosures,
    ``ComputableAnalysis.BracketContinuity.congr_point,
    ``ComputableAnalysis.BracketContinuity.congr_value,
    ``ComputableAnalysis.BracketContinuity.congr_function,
    ``ComputableAnalysis.BracketContinuity.hasContinuousAt_iff_neighborhoods,
    ``ComputableAnalysis.BracketContinuity.values_tendTo,
    ``ComputableAnalysis.BracketContinuity.rational_agreement,
    ``ComputableAnalysis.BracketContinuity.identity,
    ``ComputableAnalysis.BracketContinuity.constant,
    ``ComputableAnalysis.ScheduledIntervalRegularOn.bracketCandidate_hasEnclosureValue,
    ``ComputableAnalysis.ScheduledIntervalRegularOn.exists_continuousAt,
    ``ComputableAnalysis.IntervalRegularOn.continuousAt_closed,
    ``ComputableAnalysis.EpsilonDeltaContinuousOn.exists_continuousAt,
    ``ComputableAnalysis.HasDerivativeOnInterval.toParametrizedDerivative,
    ``ComputableAnalysis.FunctionTheory.ContinuousOn.hasEnclosureCoordinates,
    ``ComputableAnalysis.FunctionTheory.HasDerivativeAt.hasRemainderCoordinates,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.ContinuousOn.hasEnclosureCoordinates,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.HasDerivativeAt.hasRemainderCoordinates,
    ``ComputableAnalysis.ParametrizedFoundationExamples.square_continuous_closed,
    ``ComputableAnalysis.ParametrizedFoundationExamples.affine_finite_certificate,
    ``ComputableAnalysis.ParametrizedFoundationExamples.jump_not_continuous,
    ``ComputableAnalysis.RawLimit.unique,
    ``ComputableAnalysis.RawLimit.congr_target_iff,
    ``ComputableAnalysis.RawLimit.congr_sequence,
    ``ComputableAnalysis.RawLimit.bisequence_unique,
    ``ComputableAnalysis.RawLimit.bisequence_congr_target,
    ``ComputableAnalysis.BracketDerivative.unique,
    ``ComputableAnalysis.BracketDerivative.congr_point_iff,
    ``ComputableAnalysis.BracketDerivative.congr_value_iff,
    ``ComputableAnalysis.BracketDerivative.congr_function,
    ``ComputableAnalysis.BracketDerivative.clipped_admissible,
    ``ComputableAnalysis.BracketDerivative.allowance_tendsTo_zero,
    ``ComputableAnalysis.BracketDerivative.outerDerivative_hasDerivative,
    ``ComputableAnalysis.BracketDerivativeExamples.squareDerivative_hasDerivative,
    ``ComputableAnalysis.BracketDerivativeExamples.square_closed_interval,
    ``ComputableAnalysis.BracketDerivativeExamples.affine_hasDerivative,
    ``ComputableAnalysis.BracketDerivativeExamples.affinePointwise_hasDerivative,
    ``ComputableAnalysis.BracketDerivativeExamples.squarePointwise_hasDerivative,
``ComputableAnalysis.ArctanInverseCircle.cosineQuarter_valid,
    ``ComputableAnalysis.ArctanInverseCircle.quarterSlope_target,
    ``ComputableAnalysis.ArctanInverseCircle.sineQuarter_valid,
    ``ComputableAnalysis.ArctanInverseConstruction.inverse_valid,
    ``ComputableAnalysis.ArctanInverseConstruction.rational_forward_target,
    ``ComputableAnalysis.ArctanSecantFoundation.derivative_valid_and_equiv,
    ``ComputableAnalysis.ArctanSecantFoundation.hasIntegral,
    ``ComputableAnalysis.ArctanSecantFoundation.increment_bounds,
    ``ComputableAnalysis.MonotoneIntegralBounds.tight,
    ``ComputableAnalysis.SecantFoundation.cellDerivativeBounds,
    ``ComputableAnalysis.SqrtSecantFoundation.derivative_valid_and_equiv,
    ``ComputableAnalysis.SqrtSecantFoundation.positive_segment_hasIntegral,
    ``ComputableAnalysis.SquareRootSecantNewton.sqrtTwo_equiv_bisection,
    ``ComputableAnalysis.SquareRootSecantNewton.sqrtTwo_valid,
      ``ComputableAnalysis.SquareRootSecantNewton.sqrtTwo_mul_self_equiv_two,
    ``ComputableAnalysis.SquareRootSecantNewton.step_spec]
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
  liftIO <| IO.FS.writeFile "book/foundation-story/declarations.json" output.compress
  logInfo m!"Exported {names.toArray.size} checked project declarations."
