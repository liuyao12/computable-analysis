import Lean
import ComputableAnalysis.EnclosureHolomorphicExamples
import ComputableAnalysis.EnclosureHolomorphicCounterexample
open Lean Elab Command

private partial def dependencies (env : Environment) (name : Name) : StateM NameSet Unit := do
  if (← get).contains name then return
  modify (·.insert name)
  if let some info := env.find? name then
    for dep in info.type.getUsedConstants do dependencies env dep
    if let some value := info.value? (allowOpaque := true) then
      for dep in value.getUsedConstants do dependencies env dep

run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if mod.toString.startsWith "Mathlib" then throwError "Unexpected Mathlib import: {mod}"
  for root in [
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
      ``ComputableAnalysis.EnclosureHolomorphicExamples.eisensteinTaylor_agrees,``ComputableAnalysis.RawLimit.HasEnclosureValue.mono,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.rawDerivative_iff,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCounterexample.conjugation_continuous,
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
      ``ComputableAnalysis.ModularForms.DiskLambert.value_rational_agreement] do
    let axioms ← collectAxioms root
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {root}"
    logInfo m!"AUDIT {root}: {axioms}"
  for root in [``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureDifferentiable.compose,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureDifferentiable.product_derivative,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureTheory.segment_variation_bound,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureTheory.same_derivative_segment_agreement] do
    let deps := ((dependencies env root).run {}).2
    for dep in deps.toArray do
      if dep.toString.endsWith "Holomorphic.continuousDerivative" then
        throwError "Derivative continuity used by semantic theorem {root}: {dep}"
    logInfo m!"DEPENDENCY AUDIT {root}: no derivative-continuity field"
  let definitionDeps := ((dependencies env ``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureHolomorphic).run {}).2
  for dep in definitionDeps.toArray do
    if dep == ``ComputableAnalysis.RiemannHilbert.DomainFunctions.ContinuousOn ||
        dep == ``ComputableAnalysis.RiemannHilbert.DomainFunctions.Holomorphic ||
        dep.toString.startsWith "ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy." ||
        (dep.toString.startsWith "ComputableAnalysis.RiemannHilbert.RectangularContour." &&
          ((dep.toString.toLower.splitOn "cauchy").length > 1 ||
           (dep.toString.toLower.splitOn "taylor").length > 1)) then
      throwError "Analytic conclusion hidden in the holomorphic definition: {dep}"
  logInfo "CONTRACT AUDIT: holomorphicity covers all nearby computed secants; no derivative-continuity field, Cauchy or Taylor conclusion occurs in its definition"
  let continuityDeps := ((dependencies env ``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureHolomorphic.continuousDerivative).run {}).2
  unless continuityDeps.contains ``ComputableAnalysis.RiemannHilbert.DomainFunctions.HasStrictDerivativeAt.neighbor_derivative_bound do
    throwError "Missing secant comparison in derivative continuity proof"
  if continuityDeps.contains ``ComputableAnalysis.RiemannHilbert.DomainFunctions.Holomorphic.continuousDerivative then
    throwError "Derivative continuity extracted from the legacy hypothesis"
  logInfo "CONTINUITY AUDIT: first-derivative continuity proved from nearby secants; no legacy continuity field"
  for (root, required) in [
      (``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.cauchy_formula,
        [``ComputableAnalysis.RiemannHilbert.RectangularContour.fixedRectangleCauchyContour_rectangular,
         ``ComputableAnalysis.RiemannHilbert.RectangularContour.continuousRectangleBoundary_eventual_zero]),
      (``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.taylor_expansion,
        [``ComputableAnalysis.RiemannHilbert.RectangularContour.localCauchyTaylor_agrees,
         ``ComputableAnalysis.RiemannHilbert.RectangularContour.cauchyTaylorKernel_remainder_bound]),
      (``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCauchy.derivative_holomorphic,
        [``ComputableAnalysis.RiemannHilbert.RectangularContour.localCauchyDerivativeSeries_agrees,
         ``ComputableAnalysis.RiemannHilbert.BoundedSeries.derivativeCoefficients_sum])] do
    let deps := ((dependencies env root).run {}).2
    for name in required do
      unless deps.contains name do throwError "Missing constructed proof bridge {name} for {root}"
    logInfo m!"CONSTRUCTION AUDIT {root}: actual contour/series reconstruction dependencies present"
  logInfo "PASS: shrinking computed complex secant boxes; proved first-derivative continuity and exact equivalence with the previous continuous-derivative definition; two-way quantitative bridge; separate pointwise calculus and whole-segment laws; constructed Cauchy formula, exact Taylor expansion and factorial-normalized coefficients; actual higher derivative holomorphicity and continuity; elementary and full-disk special-function applications; conjugation rejected. Standard axioms only; no Mathlib imports."
