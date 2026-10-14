import Lean
import ComputableAnalysis.EnclosureHolomorphicExamples
import ComputableAnalysis.EnclosureHolomorphicCounterexample
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
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.complexSecant_congr,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.balanced_separation,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.complexSecant_error,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.HasStrictDerivativeAt.secantBound,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.HasSecantBoundAt.strict,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.HasStrictDerivativeAt.errorBoxes,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.twoPointErrorBoxes_iff,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.shrinkingSecantBoxes_iff,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.HasShrinkingSecantBoxes.secantBound,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.HasStrictDerivativeAt.pointwise,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.Holomorphic.strictAt,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.HasStrictDerivativeAt.neighbor_derivative_bound,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureHolomorphic.secantBoxes,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureHolomorphic.continuousDerivative,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.shrinkingHolomorphic_iff_continuous,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.enclosureHolomorphic_iff,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureHolomorphic.toHolomorphic,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureHolomorphic.differentiable,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureDifferentiable.compose_derivative,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureDifferentiable.product_derivative,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.cauchy_formula,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.cauchy_limit_identity,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.local_cauchy_formula,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.constructed_cauchy_formula,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.coefficient_converges,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.coefficient_representation_invariance,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.taylor_center,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.taylor_domain,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.taylor_expansion,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.taylor_prefix_error,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.taylor_representation_invariance,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.derivative_holomorphic,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.higherDerivative_domain,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.higherDerivative_holomorphic,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.higherDerivative_successor,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.coefficient_derivative_formula,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.higher_cauchy_formula,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.higherDerivative_continuous,
      ``ComputableAnalysis.EnclosureHolomorphicExamples.exponentialTaylor_agrees,
      ``ComputableAnalysis.EnclosureHolomorphicExamples.eisensteinTaylor_agrees,
    ``ComputableAnalysis.RawLimit.HasEnclosureValue.mono,
    ``ComputableAnalysis.FunctionTheory.denormalized_small,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.enclosureDerivative_iff,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.HasEnclosureDerivativeAt.unique,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.HasEnclosureDerivativeAt.congrDerivative,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.HasEnclosureDerivativeAt.congrPoint,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.Holomorphic.enclosure,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureHolomorphic.continuous,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureHolomorphic.derivative_congr,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureHolomorphic.derivative_unique,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureHolomorphic.compose,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureHolomorphic.compose_derivative,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureHolomorphic.sumOn,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureHolomorphic.productOn,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureHolomorphic.product_derivative,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureHolomorphic.negate,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureTheory.segment_variation_bound,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureTheory.zero_derivative_segment_constant,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureTheory.same_derivative_segment_agreement,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCounterexample.conjugation_not_differentiable,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCounterexample.conjugation_not_holomorphic,
    ``ComputableAnalysis.EnclosureHolomorphicExamples.polynomial,
    ``ComputableAnalysis.EnclosureHolomorphicExamples.rationalFunction,
    ``ComputableAnalysis.EnclosureHolomorphicExamples.reciprocal,
    ``ComputableAnalysis.EnclosureHolomorphicExamples.reciprocal_derivative,
    ``ComputableAnalysis.EnclosureHolomorphicExamples.exponential,
    ``ComputableAnalysis.EnclosureHolomorphicExamples.exponential_derivative,
    ``ComputableAnalysis.EnclosureHolomorphicExamples.sine,
    ``ComputableAnalysis.EnclosureHolomorphicExamples.cosine,
    ``ComputableAnalysis.EnclosureHolomorphicExamples.sine_derivative,
    ``ComputableAnalysis.EnclosureHolomorphicExamples.cosine_derivative,
    ``ComputableAnalysis.EnclosureHolomorphicExamples.logarithm,
    ``ComputableAnalysis.EnclosureHolomorphicExamples.logarithm_derivative,
    ``ComputableAnalysis.EnclosureHolomorphicExamples.lambert,
    ``ComputableAnalysis.EnclosureHolomorphicExamples.eisenstein,
    ``ComputableAnalysis.EnclosureHolomorphicExamples.eisenstein_rational_agreement,
    ``ComputableAnalysis.ElementarySineODE.powerSeries_primary_agrees,
    ``ComputableAnalysis.ElementarySineODE.sinPi_primary_agrees,
    ``ComputableAnalysis.ElementarySineODE.powerSeries_primary_converges,
    ``ComputableAnalysis.ElementarySineODE.sinPi_primary_converges,
    ``ComputableAnalysis.ModularForms.DiskLambert.value_rational_agreement,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.rawDerivative_iff,
    ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCounterexample.conjugation_continuous,
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
