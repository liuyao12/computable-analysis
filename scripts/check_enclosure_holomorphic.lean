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
  for root in [``ComputableAnalysis.RawLimit.HasEnclosureValue.mono,
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
  for root in [``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureHolomorphic.compose,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.IsEnclosureHolomorphic.product_derivative,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureTheory.segment_variation_bound,
      ``ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureTheory.same_derivative_segment_agreement] do
    let deps := ((dependencies env root).run {}).2
    for dep in deps.toArray do
      if dep.toString.endsWith "Holomorphic.continuousDerivative" then
        throwError "Derivative continuity used by semantic theorem {root}: {dep}"
    logInfo m!"DEPENDENCY AUDIT {root}: no derivative-continuity field"
  logInfo "PASS: two-way covered-enclosure derivative bridge; uniqueness and representation invariance; value continuity, chain and product rules; whole-segment variation, zero-derivative constancy and equal-derivative identification without derivative continuity; conjugation rejected; actual elementary and full-disk special-function witnesses and primary extension bridges. Standard axioms only; no Mathlib imports."
